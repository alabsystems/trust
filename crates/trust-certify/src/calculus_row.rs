// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VF5: the certificate behind a "proved (calculus)" row (proven-core plan VF5;
//! Clean `docs/DECISIONS.md` R169, R170).
//!
//! A calculus row says that one function of the compiler's trust-ir artifact
//! is safe by F1's VC calculus over SemR: the Clean theorem
//! `VF5.RowProved bytes A fid sym` (the bytes decode under SemR; function
//! `fid` is in the module under the symbol `sym`; it is `Valid_R` under the
//! annotation `A`; the closed module is `ClosedSafe`; the entry premise
//! `entriesOK` holds, so every root is safe on any well-typed valid
//! arguments). `vc_sound_F1` and `compose_F1` stand behind `row_of`, the one
//! proof this module offers, and both are admitted through the reference
//! entry with closures ⊆ Ax0 when the family's base is built.
//!
//! # The fence
//!
//! A [`CalculusRowCertificate`] is built in exactly one place,
//! [`certify_calculus_row`], which consumes the
//! [`clean_kernel::ReferenceAccepted`] token the reference entry issues for
//! the closed judgment `row_of … : RowProved bytes A fid sym`. The goal is
//! built HERE from the claim's artifact bytes, function id and symbol, so a
//! certificate cannot name a function or an artifact its judgment was not
//! about; the annotation and certificate lists come from the untrusted
//! producer and only reach the kernel. The certificate's fields are private,
//! it has no other constructor, and it is neither `Default` nor
//! `Deserialize`.
//!
//! What `RowProved` MEANS is fixed by the environment the entry checks
//! against: the family's base ([`Vf5Reference`]) is admitted only when its
//! environment digest is one of [`PINNED_VF5_ENV_DIGESTS`], so a base that
//! redefines `RowProved`, `ClosedSafe` or SemR's decoder has another digest
//! and is refused. The pinned Clean contains the VF5 family, but no measured
//! production base digest is pinned yet. Production admission stays closed
//! until an independently checked base and its input package are pinned.
//!
//! # How the certificate reaches the compiler
//!
//! Like the KR0 reference certificate, a calculus certificate travels beside
//! the rows: [`register`] records it under the function's symbol (a symbol
//! two artifacts claim is withdrawn for good), and
//! [`calculus_row_certificate_bound`] returns it only for that symbol AND the
//! artifact bytes its judgment was about. The compiler mints
//! `ResultProofAuthority::CalculusRowProved` only with one, asking with the
//! symbol its own published trust-ir module gives the body and that module's
//! own bytes, so the certificate is about this body in this compile.

use std::collections::{HashMap, HashSet};
use std::sync::{Mutex, OnceLock};

use clean_kernel::name::Name;
use clean_kernel::{EnvDigest, Expr, Level, ReferenceKernel, ReferenceRefusal};
use sha2::{Digest, Sha256};

use crate::reference_mint::ReferenceCertificate;

pub mod base;
pub mod hints;

/// The environment digests of the VF5 family bases a calculus row may be
/// checked against (the reference entry built over the family's `VF5Check`
/// cone at a pinned Clean). Empty pending independent production-base
/// measurement, so nothing is admitted (fail closed).
pub const PINNED_VF5_ENV_DIGESTS: &[[u8; 32]] = &[];

/// The constants of the family a row's judgment names; a base without any of
/// them is refused before the digest is even compared.
const REQUIRED: [&str; 4] = ["VF5.RowProved", "VF5.row_of", "VF5.checkBlob", "VF5.rowShape"];

/// The reference entry over a VF5 family base whose digest is pinned.
#[derive(Debug)]
pub struct Vf5Reference {
    kernel: ReferenceKernel,
}

/// Why no calculus certificate was issued (diagnostics and tests only; it
/// never changes a verdict).
#[derive(Debug)]
pub enum CalculusRowMiss {
    /// The base lacks a constant the judgment names.
    MissingConstant(&'static str),
    /// The base's environment digest is not pinned.
    UnpinnedBase(EnvDigest),
    /// The entry refused the judgment.
    Refused(ReferenceRefusal),
    /// The claim is empty (no artifact bytes or no symbol).
    EmptyClaim,
}

impl Vf5Reference {
    /// Admit `kernel` as the VF5 family's reference entry: it must hold the
    /// constants a row names and its digest must be pinned.
    ///
    /// # Errors
    /// [`CalculusRowMiss::MissingConstant`] or [`CalculusRowMiss::UnpinnedBase`].
    pub fn new(kernel: ReferenceKernel) -> Result<Self, CalculusRowMiss> {
        Self::with_pins(kernel, PINNED_VF5_ENV_DIGESTS)
    }

    fn with_pins(kernel: ReferenceKernel, pins: &[[u8; 32]]) -> Result<Self, CalculusRowMiss> {
        for name in REQUIRED {
            if kernel.environment().get_const(&Name::from_string(name)).is_none() {
                return Err(CalculusRowMiss::MissingConstant(name));
            }
        }
        let digest = kernel.env_digest();
        if !pins.contains(&digest.0) {
            return Err(CalculusRowMiss::UnpinnedBase(digest));
        }
        Ok(Self { kernel })
    }

    /// The pinned environment digest this entry checks against.
    #[must_use]
    pub fn env_digest(&self) -> EnvDigest {
        self.kernel.env_digest()
    }
}

/// The row a producer claims: one function of one trust-ir artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CalculusRowClaim {
    /// The artifact's bytes, exactly as the compiler wrote them.
    pub artifact: Vec<u8>,
    /// The function's index in the decoded module.
    pub fid: u64,
    /// The function's symbol in the artifact (`Function.name`, the mangled
    /// path the compiler gave it).
    pub symbol: Vec<u8>,
}

/// What the reference entry accepted for one calculus row (see the module
/// docs for the fence).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CalculusRowCertificate {
    reference: ReferenceCertificate,
    artifact_sha256: [u8; 32],
    fid: u64,
    symbol: Vec<u8>,
}

impl CalculusRowCertificate {
    /// The reference entry's certificate for the closed `RowProved` judgment.
    #[must_use]
    pub fn reference(&self) -> &ReferenceCertificate {
        &self.reference
    }

    /// SHA-256 of the artifact the judgment is about.
    #[must_use]
    pub fn artifact_sha256(&self) -> [u8; 32] {
        self.artifact_sha256
    }

    /// The function's index in the artifact.
    #[must_use]
    pub fn fid(&self) -> u64 {
        self.fid
    }

    /// The function's symbol in the artifact.
    #[must_use]
    pub fn symbol(&self) -> &[u8] {
        &self.symbol
    }

    /// Whether this certificate is about the function `symbol`.
    #[must_use]
    pub fn binds_symbol(&self, symbol: &[u8]) -> bool {
        !symbol.is_empty() && self.symbol == symbol
    }

    /// Whether this checked judgment names these exact current artifact bytes.
    /// A digest match never constructs or restores a certificate.
    #[must_use]
    pub fn binds_artifact(&self, artifact: &[u8]) -> bool {
        !artifact.is_empty() && self.artifact_sha256 == <[u8; 32]>::from(Sha256::digest(artifact))
    }
}

fn konst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), Vec::new())
}

fn konst_at(name: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(Name::from_string(name), levels)
}

/// The Lean `List Nat` literal of `bytes`, with `Nat` literals as elements.
fn nat_list(bytes: &[u8]) -> Expr {
    let nat = konst("Nat");
    let mut list = Expr::app(konst_at("List.nil", vec![Level::zero()]), nat.clone());
    for byte in bytes.iter().rev() {
        list = Expr::apps(
            konst_at("List.cons", vec![Level::zero()]),
            [nat.clone(), Expr::nat_lit(u64::from(*byte)), list],
        );
    }
    list
}

/// `true = true`'s proof, the `rfl` both of `row_of`'s Boolean premises take.
fn bool_rfl() -> Expr {
    Expr::apps(
        konst_at("Eq.refl", vec![Level::succ(Level::zero())]),
        [konst("Bool"), konst("Bool.true")],
    )
}

/// The goal `RowProved bytes A fid sym` and the proof
/// `row_of (bs := bytes) (A := A) (cs := certs) (fid := fid) (sym := sym) rfl rfl`.
fn judgment(claim: &CalculusRowClaim, annotation: &Expr, certs: &Expr) -> (Expr, Expr) {
    let bytes = nat_list(&claim.artifact);
    let sym = nat_list(&claim.symbol);
    let fid = Expr::nat_lit(claim.fid);
    let goal = Expr::apps(
        konst("VF5.RowProved"),
        [bytes.clone(), annotation.clone(), fid.clone(), sym.clone()],
    );
    let proof = Expr::apps(
        konst("VF5.row_of"),
        [bytes, annotation.clone(), certs.clone(), fid, sym, bool_rfl(), bool_rfl()],
    );
    (goal, proof)
}

/// Check one calculus row through the VF5 reference entry and issue its
/// certificate. `annotation` (`A : Nat → List Cons`) and `certs` (the Farkas
/// certificates per function) are the untrusted producer's; the kernel
/// decides whether `checkBlob` and `rowShape` hold of them by evaluation.
///
/// # Errors
/// [`CalculusRowMiss::EmptyClaim`] for a claim with no bytes or no symbol,
/// [`CalculusRowMiss::Refused`] when the entry refuses the judgment.
pub fn certify_calculus_row(
    reference: &Vf5Reference,
    claim: &CalculusRowClaim,
    annotation: &Expr,
    certs: &Expr,
) -> Result<CalculusRowCertificate, CalculusRowMiss> {
    certify_calculus_judgment(reference, claim, annotation, certs).map(|checked| checked.certificate)
}

/// The actual checked pair, retained only by a fresh isolated presentation.
/// This is not deserializable and exposes no new entry/acceptance predicate.
struct CheckedJudgment {
    certificate: CalculusRowCertificate,
    goal: Expr,
    proof: Expr,
}

/// The one private kernel check shared by production minting and descriptive
/// observations of an actual completed base. Only the production caller may
/// turn this token into a certificate; observations drop it before returning.
struct KernelJudgment {
    accepted: clean_kernel::ReferenceAccepted,
    goal: Expr,
    proof: Expr,
}

fn check_calculus_judgment(
    kernel: &ReferenceKernel,
    claim: &CalculusRowClaim,
    annotation: &Expr,
    certs: &Expr,
) -> Result<KernelJudgment, CalculusRowMiss> {
    if claim.artifact.is_empty() || claim.symbol.is_empty() {
        return Err(CalculusRowMiss::EmptyClaim);
    }
    let (goal, proof) = judgment(claim, annotation, certs);
    let accepted = kernel.check_closed_term(&goal, &proof).map_err(CalculusRowMiss::Refused)?;
    Ok(KernelJudgment { accepted, goal, proof })
}

fn certify_calculus_judgment(
    reference: &Vf5Reference,
    claim: &CalculusRowClaim,
    annotation: &Expr,
    certs: &Expr,
) -> Result<CheckedJudgment, CalculusRowMiss> {
    let KernelJudgment { accepted, goal, proof } =
        check_calculus_judgment(&reference.kernel, claim, annotation, certs)?;
    let certificate = CalculusRowCertificate {
        reference: ReferenceCertificate::from_accepted(accepted),
        artifact_sha256: Sha256::digest(&claim.artifact).into(),
        fid: claim.fid,
        symbol: claim.symbol.clone(),
    };
    Ok(CheckedJudgment { certificate, goal, proof })
}

// ---------------------------------------------------------------------------
// The side table: symbol -> certificate.
// ---------------------------------------------------------------------------

/// Most certificates one process records; past it nothing more is recorded,
/// so a further row mints nothing (fail closed).
const MAX_REGISTERED: usize = 1 << 16;

/// The recorded certificates by symbol, and the symbols withdrawn for good.
#[derive(Default)]
struct Table {
    recorded: HashMap<Vec<u8>, CalculusRowCertificate>,
    /// Symbols two artifacts claimed. Withdrawal is sticky: once two
    /// certificates disagree about which artifact a symbol's function is in,
    /// neither, and no later one, is believed for it in this process.
    withdrawn: HashSet<Vec<u8>>,
}

fn table() -> &'static Mutex<Table> {
    static TABLE: OnceLock<Mutex<Table>> = OnceLock::new();
    TABLE.get_or_init(|| Mutex::new(Table::default()))
}

/// Record `certificate` under its function's symbol. A symbol already
/// recorded under a DIFFERENT artifact is withdrawn instead, and stays
/// withdrawn: two artifacts claim one function, so neither is believed, and a
/// later registration of either (or of a third) records nothing for it.
pub fn register(certificate: CalculusRowCertificate) {
    let Ok(mut table) = table().lock() else { return };
    if table.withdrawn.contains(&certificate.symbol) {
        return;
    }
    match table.recorded.get(&certificate.symbol) {
        Some(existing) if existing.artifact_sha256 != certificate.artifact_sha256 => {
            table.recorded.remove(&certificate.symbol);
            table.withdrawn.insert(certificate.symbol);
        }
        Some(_) => {}
        None if table.recorded.len() < MAX_REGISTERED => {
            table.recorded.insert(certificate.symbol.clone(), certificate);
        }
        None => {}
    }
}

/// The calculus certificate recorded for the function `symbol` in this
/// process, or `None` (none recorded, or the symbol withdrawn).
#[must_use]
pub fn calculus_row_certificate_for(symbol: &[u8]) -> Option<CalculusRowCertificate> {
    if symbol.is_empty() {
        return None;
    }
    table().lock().ok()?.recorded.get(symbol).cloned()
}

/// The calculus certificate recorded for `symbol` that is about `artifact`:
/// the certificate names `symbol` and its judgment was about exactly these
/// bytes (their SHA-256 is the certificate's). The compiler's mint asks this
/// with the symbol and the bytes of the trust-ir module THIS compile
/// published, so a certificate about another crate's artifact (another
/// `-C metadata`, another version) or a stale one (the body changed since)
/// mints nothing.
#[must_use]
pub fn calculus_row_certificate_bound(
    symbol: &[u8],
    artifact: &[u8],
) -> Option<CalculusRowCertificate> {
    let certificate = calculus_row_certificate_for(symbol)?;
    let digest: [u8; 32] = Sha256::digest(artifact).into();
    (certificate.binds_symbol(symbol) && certificate.artifact_sha256 == digest)
        .then_some(certificate)
}

/// Whether any calculus certificate is recorded in this process. The compiler
/// asks before it looks a body up, so a process with none (every production
/// process today) does no calculus work at all.
#[must_use]
pub fn any_registered() -> bool {
    table().lock().is_ok_and(|table| !table.recorded.is_empty())
}

/// A test door (the unit tests here, and the compiler's calculus-mint tests
/// through the `calculus-row-test-support` feature, which only a
/// dev-dependency turns on): a stand-in VF5 family and a pin of its digest.
/// Production never reaches it, so production admits only
/// [`PINNED_VF5_ENV_DIGESTS`].
#[cfg(any(test, feature = "calculus-row-test-support"))]
pub mod test_support {
    use clean_kernel::{BinderInfo, Declaration, Environment};

    use super::*;

    fn nat() -> Expr {
        konst("Nat")
    }

    fn list_nat() -> Expr {
        Expr::app(konst_at("List", vec![Level::zero()]), nat())
    }

    fn bool_() -> Expr {
        konst("Bool")
    }

    fn pi(ty: Expr, body: Expr) -> Expr {
        Expr::pi(BinderInfo::Default, ty, body)
    }

    fn lam(ty: Expr, body: Expr) -> Expr {
        Expr::lam(BinderInfo::Default, ty, body)
    }

    fn def(name: &str, type_: Expr, value: Expr) -> Declaration {
        Declaration::Definition {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
            value,
            is_reducible: false,
        }
    }

    fn eq_true(lhs: Expr) -> Expr {
        Expr::apps(
            konst_at("Eq", vec![Level::succ(Level::zero())]),
            [bool_(), lhs, konst("Bool.true")],
        )
    }

    /// A stand-in family with the shapes the judgment names (`A` and the
    /// certificates are `Nat` here): `checkBlob` trivial, `rowShape` holding
    /// exactly when the function id equals `A`, and `RowProved` being
    /// `rowShape = true`, so the kernel's evaluation decides which claims are
    /// accepted. `shape_ok` false makes `rowShape` refuse everything.
    #[must_use]
    pub fn toy_kernel(shape_ok: bool) -> ReferenceKernel {
        let mut env = Environment::with_prelude();
        // checkBlob : List Nat → Nat → Nat → Bool := fun _ _ _ => true
        env.add_decl(def(
            "VF5.checkBlob",
            pi(list_nat(), pi(nat(), pi(nat(), bool_()))),
            lam(list_nat(), lam(nat(), lam(nat(), konst("Bool.true")))),
        ))
        .expect("checkBlob");
        // rowShape : List Nat → Nat → Nat → List Nat → Bool
        //   := fun _ A fid _ => Nat.beq fid A   (the kernel's evaluation decides it)
        let shape_body = if shape_ok {
            Expr::apps(konst("Nat.beq"), [Expr::bvar(1), Expr::bvar(2)])
        } else {
            konst("Bool.false")
        };
        env.add_decl(def(
            "VF5.rowShape",
            pi(list_nat(), pi(nat(), pi(nat(), pi(list_nat(), bool_())))),
            lam(list_nat(), lam(nat(), lam(nat(), lam(list_nat(), shape_body)))),
        ))
        .expect("rowShape");
        // RowProved bs A fid sym := rowShape bs A fid sym = true
        let row_body = eq_true(Expr::apps(
            konst("VF5.rowShape"),
            [Expr::bvar(3), Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)],
        ));
        env.add_decl(def(
            "VF5.RowProved",
            pi(list_nat(), pi(nat(), pi(nat(), pi(list_nat(), Expr::prop())))),
            lam(list_nat(), lam(nat(), lam(nat(), lam(list_nat(), row_body)))),
        ))
        .expect("RowProved");
        // row_of : ∀ bs A cs fid sym, checkBlob bs A cs = true →
        //   rowShape bs A fid sym = true → RowProved bs A fid sym := fun … _ hs => hs
        // Binders, outermost first: bs A cs fid sym h hs.
        let check = eq_true(Expr::apps(
            konst("VF5.checkBlob"),
            [Expr::bvar(4), Expr::bvar(3), Expr::bvar(2)],
        ));
        let shape_under_h = eq_true(Expr::apps(
            konst("VF5.rowShape"),
            [Expr::bvar(5), Expr::bvar(4), Expr::bvar(2), Expr::bvar(1)],
        ));
        let row_under_hs = Expr::apps(
            konst("VF5.RowProved"),
            [Expr::bvar(6), Expr::bvar(5), Expr::bvar(3), Expr::bvar(2)],
        );
        let row_of_ty = pi(
            list_nat(),
            pi(
                nat(),
                pi(
                    nat(),
                    pi(
                        nat(),
                        pi(list_nat(), pi(check.clone(), pi(shape_under_h.clone(), row_under_hs))),
                    ),
                ),
            ),
        );
        let row_of_val = lam(
            list_nat(),
            lam(
                nat(),
                lam(
                    nat(),
                    lam(nat(), lam(list_nat(), lam(check, lam(shape_under_h, Expr::bvar(0))))),
                ),
            ),
        );
        env.add_decl(Declaration::Theorem {
            name: Name::from_string("VF5.row_of"),
            level_params: vec![],
            type_: row_of_ty,
            value: row_of_val,
        })
        .expect("row_of");
        ReferenceKernel::new(env).expect("the stand-in base passes the entry")
    }

    /// `kernel` admitted as a VF5 base under a pin of its own digest: how a
    /// test reaches the real family, which no production pin names yet.
    ///
    /// # Errors
    /// [`CalculusRowMiss::MissingConstant`] for a base without the family.
    pub fn pin_own_digest(kernel: ReferenceKernel) -> Result<Vf5Reference, CalculusRowMiss> {
        let digest = kernel.env_digest().0;
        Vf5Reference::with_pins(kernel, &[digest])
    }

    /// The stand-in family admitted under a pin of its own digest.
    ///
    /// # Panics
    /// When the stand-in is not admitted.
    #[must_use]
    pub fn pinned_toy(shape_ok: bool) -> Vf5Reference {
        let kernel = toy_kernel(shape_ok);
        let digest = kernel.env_digest().0;
        Vf5Reference::with_pins(kernel, &[digest]).expect("pinned")
    }

    /// A certified stand-in row for `symbol` at function 0 (annotation 0).
    ///
    /// # Panics
    /// When the stand-in refuses it.
    #[must_use]
    pub fn certified_toy_row(symbol: &[u8], artifact: &[u8]) -> CalculusRowCertificate {
        let claim =
            CalculusRowClaim { artifact: artifact.to_vec(), fid: 0, symbol: symbol.to_vec() };
        certify_calculus_row(&pinned_toy(true), &claim, &Expr::nat_lit(0), &Expr::nat_lit(0))
            .expect("the stand-in accepts function 0 under annotation 0")
    }
}

#[cfg(test)]
mod tests {
    use clean_kernel::Environment;

    use super::test_support::toy_kernel;
    use super::*;

    fn pinned(kernel: ReferenceKernel) -> Vf5Reference {
        let digest = kernel.env_digest().0;
        Vf5Reference::with_pins(kernel, &[digest]).expect("pinned")
    }

    fn claim(symbol: &[u8], fid: u64) -> CalculusRowClaim {
        CalculusRowClaim { artifact: vec![84, 82, 85, 83, 84], fid, symbol: symbol.to_vec() }
    }

    /// A row the entry accepts is certified, bound to its symbol and artifact.
    /// Negative controls on the same entry: a function id the kernel's
    /// evaluation refuses, and an empty claim; a certificate for another symbol
    /// is a certificate of another judgment.
    #[test]
    fn a_row_the_entry_accepts_is_certified_and_bound_to_its_symbol() {
        let reference = pinned(toy_kernel(true));
        let a = Expr::nat_lit(0);
        let certified =
            certify_calculus_row(&reference, &claim(b"s", 0), &a, &a).expect("accepted");
        assert!(certified.binds_symbol(b"s"));
        assert!(!certified.binds_symbol(b"t"));
        assert!(!certified.binds_symbol(b""));
        assert_eq!(certified.fid(), 0);
        assert_eq!(
            certified.artifact_sha256(),
            <[u8; 32]>::from(Sha256::digest([84, 82, 85, 83, 84]))
        );
        assert_eq!(certified.reference().theory_id(), clean_kernel::TheoryId::LeanReferenceV1);
        assert_eq!(certified.reference().env_digest(), reference.env_digest());
        let refused = certify_calculus_row(&reference, &claim(b"s", 1), &a, &a);
        assert!(matches!(refused, Err(CalculusRowMiss::Refused(_))), "{refused:?}");
        let other = certify_calculus_row(&reference, &claim(b"t", 0), &a, &a).expect("accepted");
        assert_ne!(other.reference().decl_digest(), certified.reference().decl_digest());
        assert!(other.binds_symbol(b"t") && !other.binds_symbol(b"s"));
        assert!(matches!(
            certify_calculus_row(&reference, &claim(b"", 0), &a, &a),
            Err(CalculusRowMiss::EmptyClaim)
        ));
    }

    /// The meaning of `RowProved` is the pinned base's: a base whose digest is
    /// not pinned is refused, and so is one missing a constant. Control: the
    /// same base pinned is admitted; a base whose `rowShape` refuses every row
    /// certifies none.
    #[test]
    fn only_a_pinned_family_base_is_admitted() {
        assert!(matches!(
            Vf5Reference::new(toy_kernel(true)),
            Err(CalculusRowMiss::UnpinnedBase(_))
        ));
        let other = toy_kernel(true);
        assert!(matches!(
            Vf5Reference::with_pins(other, &[[0; 32]]),
            Err(CalculusRowMiss::UnpinnedBase(_))
        ));
        let empty = ReferenceKernel::new(Environment::with_prelude()).expect("prelude");
        let digest = empty.env_digest().0;
        assert!(matches!(
            Vf5Reference::with_pins(empty, &[digest]),
            Err(CalculusRowMiss::MissingConstant("VF5.RowProved"))
        ));
        let strict = pinned(toy_kernel(false));
        let a = Expr::nat_lit(0);
        assert!(matches!(
            certify_calculus_row(&strict, &claim(b"s", 0), &a, &a),
            Err(CalculusRowMiss::Refused(_))
        ));
        // No production pin before the family is in the pinned Clean.
        assert!(PINNED_VF5_ENV_DIGESTS.is_empty());
    }

    /// The side table returns a certificate only for its own symbol, and
    /// withdraws a symbol two artifacts claim. Control: re-registering the
    /// same certificate keeps it.
    #[test]
    fn the_side_table_binds_symbols_and_withdraws_a_conflict() {
        let reference = pinned(toy_kernel(true));
        let a = Expr::nat_lit(0);
        let mut row = claim(b"s", 0);
        let first = certify_calculus_row(&reference, &row, &a, &a).expect("accepted");
        register(first.clone());
        assert!(any_registered());
        assert_eq!(calculus_row_certificate_for(b"s"), Some(first.clone()));
        assert_eq!(calculus_row_certificate_for(b"t"), None);
        assert_eq!(calculus_row_certificate_for(b""), None);
        register(first.clone());
        assert_eq!(calculus_row_certificate_for(b"s"), Some(first));
        row.artifact.push(0);
        let second = certify_calculus_row(&reference, &row, &a, &a).expect("accepted");
        register(second);
        assert_eq!(calculus_row_certificate_for(b"s"), None, "two artifacts claim `s`");
    }

    /// Review finding 2: withdrawal is sticky. After two artifacts claimed a
    /// symbol, registering either of them again (or a third) records nothing
    /// for it. Negative control: the same sequence on a symbol no conflict
    /// touched records the certificate.
    #[test]
    fn a_withdrawn_symbol_stays_withdrawn() {
        let reference = pinned(toy_kernel(true));
        let a = Expr::nat_lit(0);
        let on = |symbol: &[u8], artifact: &[u8]| {
            let row =
                CalculusRowClaim { artifact: artifact.to_vec(), fid: 0, symbol: symbol.to_vec() };
            certify_calculus_row(&reference, &row, &a, &a).expect("accepted")
        };
        let c1 = on(b"sticky", &[1]);
        let c2 = on(b"sticky", &[2]);
        register(c1.clone());
        register(c2.clone());
        assert_eq!(calculus_row_certificate_for(b"sticky"), None);
        register(c2);
        assert_eq!(calculus_row_certificate_for(b"sticky"), None, "the second again");
        register(c1);
        assert_eq!(calculus_row_certificate_for(b"sticky"), None, "the first again");
        register(on(b"sticky", &[3]));
        assert_eq!(calculus_row_certificate_for(b"sticky"), None, "a third artifact");
        // Control.
        let fresh = on(b"untouched", &[2]);
        register(fresh.clone());
        assert_eq!(calculus_row_certificate_for(b"untouched"), Some(fresh));
    }

    /// Review finding 1: the lookup the compiler mints from binds the
    /// certificate to the artifact bytes as well as the symbol. A certificate
    /// about artifact X is returned for X and refused for any other bytes (a
    /// stale artifact, another crate's), and for another symbol. Control: the
    /// exact bytes and symbol return it.
    #[test]
    fn the_bound_lookup_needs_the_certificates_own_artifact() {
        let reference = pinned(toy_kernel(true));
        let a = Expr::nat_lit(0);
        let artifact = vec![0xde, 0xad];
        let row = CalculusRowClaim {
            artifact: artifact.clone(),
            fid: 0,
            symbol: b"_RNvCs1234_6revfoo1f".to_vec(),
        };
        let certificate = certify_calculus_row(&reference, &row, &a, &a).expect("accepted");
        register(certificate.clone());
        assert_eq!(
            calculus_row_certificate_bound(b"_RNvCs1234_6revfoo1f", &artifact),
            Some(certificate),
            "the certificate's own symbol and bytes"
        );
        assert_eq!(calculus_row_certificate_bound(b"_RNvCs1234_6revfoo1f", &[0xde, 0xae]), None);
        assert_eq!(calculus_row_certificate_bound(b"_RNvCs1234_6revfoo1f", &[0xde]), None);
        assert_eq!(calculus_row_certificate_bound(b"_RNvCs1234_6revfoo1f", &[]), None);
        assert_eq!(calculus_row_certificate_bound(b"_RNvCsZZZZ_6revfoo1f", &artifact), None);
        assert_eq!(calculus_row_certificate_bound(b"", &artifact), None);
    }
}
