//! The theorems two Clean proof files must keep proving, and the multiply cap
//! one of them is coupled to, named ONCE.
//!
//! - `proofs/codegen-equivalence/g16_multiplier_equivalence.lean` proves ay's
//!   shift-and-add array multiplier correct ([`G16_HEADLINE_THEOREMS`]) and
//!   reduces the ay-blast correspondence to two obligations
//!   ([`G16_REDUCTION_THEOREMS`], [`MODEL_MATCH_THEOREM`],
//!   [`DISCHARGE_THEOREM`]). While [`DISCHARGE_THEOREM`] is unproved,
//!   `MAX_RECHECKABLE_MUL_WIDTH` in `crates/trust-cg-bridge/src/verify_output.rs`
//!   must stay [`EXPECTED_MUL_WIDTH_CAP`]: the cap and the open obligation are
//!   the same fact (`tests/ay_blast_correspondence_gate.rs`'s header).
//! - `proofs/trust-soundness/i128_mul_corner_bounds.lean` proves the interval
//!   law `trust-vcgen`'s `v2_signed_mul_provably_cannot_overflow` rests on when
//!   it mints no i128 `Mul` overflow obligation ([`CORNER_BOUNDS_THEOREMS`]).
//!
//! The in-process half, this module's `tests`, is the authority. It checks each
//! file with `trust_certify::clean_island` (the parser, elaborator and CIC
//! kernel linked into this crate at the pinned `first-party/clean` revision),
//! so nothing is discovered and nothing can skip. A required name holds only
//! when the file itself REGISTERS it, which means the strict island policy
//! accepted it (no axiom, valueless opaque, `sorry`, `unsafe` or `partial` leaf,
//! and a clean certification audit of its proof), AND
//! [`CleanIslandSession::audit_cited_theorem`] accepts it: it is a `theorem`, not
//! a `def` of the same name, and its whole transitive closure is free of
//! non-foundational axioms. That is the in-process counterpart of
//! `clean export-cert`'s `all_axiom_closures_foundational_only` flag plus its
//! `exported_theorems` list. The statements of the load-bearing theorems
//! ([`G16_PINS`], [`CORNER_BOUNDS_PINS`]) are pinned too, structurally
//! ([`StatementPin`]), which neither the binary gates nor the name checks do.
//! The red controls in `tests` pin that it refuses a theorem leaning on an
//! axiom, a definition wearing a theorem's name, and a required theorem
//! restated under its own name.
//!
//! The binary half is the three `clean`-executable cross-checks in `tests/`
//! (`ay_blast_correspondence_gate`, `structured_multiplier_proof_gate`,
//! `i128_corner_bounds_proof_gate`). They read these same constants and run
//! only with `TRUST_CLEAN_BIN` ([`crate::clean_test_support`]).
//!
//! Until 2026-10-09 the names and the cap coupling were asserted ONLY by those
//! binary gates, which returned green with a NOTICE whenever no `clean`
//! executable was discoverable: in every fresh clone and worktree, deleting
//! `CornerBox.mul_box_upper` or raising the cap passed every lane.
//!
//! Lanes: `fast.clean-proof-obligations` runs `tests`, and so does the push
//! lane's `CROSS_CRATE_INSTRUMENTS` entry (`scripts/check_crates_tests_scoped.py`)
//! when `proofs/codegen-equivalence/`, `proofs/trust-soundness/`,
//! `crates/trust-cg-bridge/src/` or trust-certify's `src/clean_island*` (the
//! checker these tests judge with) changes.
//!
//! [`CleanIslandSession::audit_cited_theorem`]: trust_certify::clean_island::CleanIslandSession::audit_cited_theorem

use std::path::{Path, PathBuf};

/// The G16 multiplier proof, relative to the repository root.
pub const G16_MULTIPLIER_PROOF: &str = "proofs/codegen-equivalence/g16_multiplier_equivalence.lean";

/// The bounded-corner-multiply proof, relative to the repository root.
pub const CORNER_BOUNDS_PROOF: &str = "proofs/trust-soundness/i128_mul_corner_bounds.lean";

/// The bridge source that declares `MAX_RECHECKABLE_MUL_WIDTH`, relative to the
/// repository root.
pub const MUL_WIDTH_CAP_SOURCE: &str = "crates/trust-cg-bridge/src/verify_output.rs";

/// G16's headline theorems: the array multiplier equals the separately-stated
/// IR one (`mul_equiv`), and its ripple adder computes the genuine integer sum
/// (`addval`, `addval_step`); `mul_distinct` keeps the two from being one
/// definition under two names.
pub const G16_HEADLINE_THEOREMS: &[&str] =
    &["G16Mul.mul_equiv", "G16Mul.addval", "G16Mul.addval_step", "G16Mul.mul_distinct"];

/// The reduction: everything downstream of the correspondence hypothesis. All
/// must be real, axiom-free Theorems.
pub const G16_REDUCTION_THEOREMS: &[&str] = &[
    "G16Mul.mul_equiv",
    "G16Mul.addval",
    "G16Mul.blast_equals_ir",
    "G16Mul.blast_value_eq",
    "G16Mul.agreement_is_discriminating",
    // The faithfulness witnesses for `mul_ay`. These are `rfl`, so the kernel
    // COMPUTES both multipliers and compares words — without them the
    // decomposition could drift from ay's loop and nothing would notice.
    "G16Mul.ay_w1",
    "G16Mul.ay_w3",
    // First brick of obligation 2.
    "G16Mul.shlk_shl1",
    // Obligation 2 verified EXHAUSTIVELY at widths 1..5 — every pair of n-bit
    // words, 1_364 pairs, all carry patterns. `rfl`, so the kernel COMPUTES
    // both multipliers over the enumerated word lists.
    "G16Mul.exh1",
    "G16Mul.exh4",
    "G16Mul.exh5",
    // The negative control that makes those exhaustive theorems mean something:
    // the same harness pointed at the WRONG function reports false. Without it
    // a `checkAB` that could not distinguish anything would satisfy them
    // vacuously.
    "G16Mul.exh_negative_control",
    // The arithmetic half of ripple-adder associativity, proved from the bare
    // prelude: two words of the SAME LENGTH with the SAME VALUE are the same
    // word. This is the piece obligation 2's general proof was blocked on.
    "G16Mul.toNat_inj",
    "G16Mul.double_cancel",
    "G16Mul.parity_cons",
    // The length hypothesis of toNat_inj is load-bearing, not bookkeeping:
    // [] and [false] share a value and differ in length, so dropping it would
    // make the theorem FALSE.
    "G16Mul.toNat_len_needed",
    "G16Mul.llen_len_differs",
    // Lemma 1 of the three associativity needs: the value law at equal lengths,
    // plus the bound and uniqueness step that turn a value equation back into a
    // bit equation.
    "G16Mul.wadd_value",
    "G16Mul.toNat_lt_pow2",
    "G16Mul.carry_unique",
    "G16Mul.lt_absurd",
    "G16Mul.llen_addRec",
    "G16Mul.toNatN_eq_toNat",
    // Lemma (a): RIPPLE-ADDER ASSOCIATIVITY, and the general remainder
    // uniqueness it needs (the two carry corrections ADD, reaching 2).
    "G16Mul.wadd_assoc",
    "G16Mul.rem_unique",
    // Its non-vacuity: the two groupings genuinely produce DIFFERENT carry-outs
    // while agreeing on the result, which is why a bit-wise proof is impossible
    // and the value route was required.
    "G16Mul.assoc_carries_differ",
    "G16Mul.assoc_witness",
    // Lemma (b): the low bits of a sum depend only on the low bits of the
    // operands, and the shift distribution it yields.
    "G16Mul.droplast_addRec",
    "G16Mul.shl1_wadd",
    // Lemma (c) and the discharge of obligation 2 itself.
    "G16Mul.accRows_lemma",
    "G16Mul.addRec_zeros",
    "G16Mul.shlk_wadd",
];

/// The name a proof of OBLIGATION 2 (`mul_ay = mul_m`, pure mathematics, fully
/// inside clean) takes. It is proved, and must stay proved: it is the only half
/// of the correspondence clean can prove.
pub const MODEL_MATCH_THEOREM: &str = "G16Mul.mul_ay_matches_model";

/// The name a proof of OBLIGATION 1 (ay's Rust encoder emits `mul_ay`) MUST
/// take when it lands. Naming it in advance is what lets the coupling detect
/// the transition rather than silently keep passing.
pub const DISCHARGE_THEOREM: &str = "G16Mul.ay_blast_agrees";

/// The cap that must stay in force while [`DISCHARGE_THEOREM`] is absent.
pub const EXPECTED_MUL_WIDTH_CAP: u32 = 8;

/// The interval law the i128 `Mul` suppression rests on (`mul_box_*`), and the
/// witnesses that keep the development from degenerating into statements about
/// a multiplication that computes to nothing.
pub const CORNER_BOUNDS_THEOREMS: &[&str] = &[
    "CornerBox.mul_box_upper",
    "CornerBox.mul_box_lower",
    "CornerBox.imul_comm",
    "CornerBox.corner_witness_products",
    "CornerBox.corner_witness_negative",
];

/// What a [`StatementPin`] fixes about its constant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PinnedPart {
    /// A theorem's statement: its kernel type.
    Statement,
    /// A `Prop`-valued definition's body, for a definition a pinned statement
    /// is phrased in (`G16Mul.addval : ∀ xs, AddVal xs` says nothing if
    /// `AddVal` becomes `True`).
    Definition,
}

/// A required name holds only while the constant still says what it said
/// when its name was required: registered, axiom-free and a `theorem` is not
/// enough, because `theorem corner_witness_negative : True := True.intro` is
/// all three. [`Self::term`] is elaborated in the constant's namespace as the
/// body of `def <pin> : <ty> := <term>`, and the kernel term must EQUAL the
/// constant's own (its type for [`PinnedPart::Statement`], its body for
/// [`PinnedPart::Definition`]) up to bound-variable names. Structural, not
/// definitional: a closed `rfl` witness restated as the value it computes to
/// (`corner_witness_negative` as `Eq Int (Int.negOfNat 6) (Int.negOfNat 6)`,
/// one of the red controls) is the same proposition to the kernel and is
/// still refused.
///
/// The definitions those statements apply (`mul_m`, `mul_ir`, `mul_ay`,
/// `wadd_m`, ...) are not pinned: `mul_distinct` and the exhaustive `rfl`
/// witnesses are what keep them from collapsing into one another.
#[derive(Clone, Copy, Debug)]
pub struct StatementPin {
    /// The pinned constant, namespace-qualified.
    pub constant: &'static str,
    /// What of it is pinned.
    pub part: PinnedPart,
    /// The type [`Self::term`] has: `Prop` for every theorem statement.
    pub ty: &'static str,
    /// The term, in the proof file's own notation, as written inside the
    /// constant's namespace.
    pub term: &'static str,
}

/// The statements of [`G16_HEADLINE_THEOREMS`] and [`MODEL_MATCH_THEOREM`],
/// and the two `Prop` definitions they are phrased in. The reduction lemmas
/// are required by name only: their content reaches the pinned
/// `mul_ay_matches_model`, which must stay axiom-free whatever it cites.
pub const G16_PINS: &[StatementPin] = &[
    StatementPin {
        constant: "G16Mul.mul_equiv",
        part: PinnedPart::Statement,
        ty: "Prop",
        term: "∀ (a : List Bool) (b : List Bool), mul_m a b = mul_ir a b",
    },
    StatementPin {
        constant: "G16Mul.addval",
        part: PinnedPart::Statement,
        ty: "Prop",
        term: "∀ (xs : List Bool), AddVal xs",
    },
    StatementPin {
        constant: "G16Mul.addval_step",
        part: PinnedPart::Statement,
        ty: "Prop",
        term: "∀ (a : Bool) (as_ : List Bool), AddVal as_ → AddVal (List.cons a as_)",
    },
    StatementPin {
        constant: "G16Mul.AddVal",
        part: PinnedPart::Definition,
        ty: "List Bool → Prop",
        term: "fun (xs : List Bool) => ∀ (ys : List Bool) (c : Bool), \
               Nat.add (toNat (addRec_m xs ys c)) (Nat.mul (pow2 (llen xs)) (b2n (carryOut_m xs ys c))) \
               = Nat.add (Nat.add (toNat xs) (toNatN xs ys)) (b2n c)",
    },
    StatementPin {
        constant: "G16Mul.mul_distinct",
        part: PinnedPart::Statement,
        ty: "Prop",
        term: "wordBeq (mul_m [false,true,false,false] [true,true,false,false]) \
               (wadd_m [false,true,false,false] [true,true,false,false]) = false",
    },
    StatementPin {
        constant: MODEL_MATCH_THEOREM,
        part: PinnedPart::Statement,
        ty: "Prop",
        term: "AyModelMatches",
    },
    StatementPin {
        constant: "G16Mul.AyModelMatches",
        part: PinnedPart::Definition,
        ty: "Prop",
        term: "∀ (a : List Bool) (b : List Bool), mul_ay a b = mul_m a b",
    },
];

/// The statements of every [`CORNER_BOUNDS_THEOREMS`] entry: the interval law
/// itself and its non-vacuity witnesses. They mention prelude `Int` only.
pub const CORNER_BOUNDS_PINS: &[StatementPin] = &[
    StatementPin {
        constant: "CornerBox.mul_box_upper",
        part: PinnedPart::Statement,
        ty: "Prop",
        term: "∀ (la ha lb hb a b M : Int), \
               Int.le la a → Int.le a ha → Int.le lb b → Int.le b hb → \
               Int.le (Int.mul la lb) M → Int.le (Int.mul la hb) M → \
               Int.le (Int.mul ha lb) M → Int.le (Int.mul ha hb) M → \
               Int.le (Int.mul a b) M",
    },
    StatementPin {
        constant: "CornerBox.mul_box_lower",
        part: PinnedPart::Statement,
        ty: "Prop",
        term: "∀ (la ha lb hb a b m : Int), \
               Int.le la a → Int.le a ha → Int.le lb b → Int.le b hb → \
               Int.le m (Int.mul la lb) → Int.le m (Int.mul la hb) → \
               Int.le m (Int.mul ha lb) → Int.le m (Int.mul ha hb) → \
               Int.le m (Int.mul a b)",
    },
    StatementPin {
        constant: "CornerBox.imul_comm",
        part: PinnedPart::Statement,
        ty: "Prop",
        term: "∀ (a b : Int), Eq Int (Int.mul a b) (Int.mul b a)",
    },
    StatementPin {
        constant: "CornerBox.corner_witness_products",
        part: PinnedPart::Statement,
        ty: "Prop",
        term: "Eq Int (Int.mul (Int.ofNat 3) (Int.ofNat 4)) (Int.ofNat 12)",
    },
    StatementPin {
        constant: "CornerBox.corner_witness_negative",
        part: PinnedPart::Statement,
        ty: "Prop",
        term: "Eq Int (Int.mul (Int.negSucc 1) (Int.ofNat 3)) (Int.negOfNat 6)",
    },
];

/// The Clean source declaring one `def` per pin, the `i`th named
/// `<namespace>.trust_statement_pin_<i>`, in its constant's namespace so the
/// term reads as the proof file writes it.
#[must_use]
pub fn statement_pin_source(pins: &[StatementPin]) -> String {
    pins.iter()
        .enumerate()
        .map(|(i, pin)| {
            let namespace = pin_namespace(pin);
            format!(
                "namespace {namespace}\ndef trust_statement_pin_{i} : {} :=\n  {}\nend {namespace}\n",
                pin.ty, pin.term
            )
        })
        .collect()
}

/// The namespace-qualified name [`statement_pin_source`] gives the `i`th pin.
#[must_use]
pub fn statement_pin_name(pins: &[StatementPin], i: usize) -> String {
    format!("{}.trust_statement_pin_{i}", pin_namespace(&pins[i]))
}

fn pin_namespace(pin: &StatementPin) -> &'static str {
    pin.constant
        .rsplit_once('.')
        .map(|(namespace, _)| namespace)
        .unwrap_or_else(|| panic!("pinned constant {} is not namespaced", pin.constant))
}

/// This checkout's root, from the crate's compile-time manifest directory.
#[must_use]
pub fn repo_root() -> PathBuf {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    manifest
        .join("../..")
        .canonicalize()
        .unwrap_or_else(|e| panic!("repo root above {} must resolve: {e}", manifest.display()))
}

/// `relative` under [`repo_root`].
#[must_use]
pub fn repo_path(relative: &str) -> PathBuf {
    repo_root().join(relative)
}

/// The value of `const MAX_RECHECKABLE_MUL_WIDTH` in `source`, read from the
/// text so the coupling is against the value the bridge ACTUALLY compiles with,
/// not a copy of it here. Exactly one declaration line is accepted: with two
/// (a `#[cfg(test)]` / `#[cfg(not(test))]` pair, say) a text reader cannot know
/// which one the bridge compiles with, and the first would be read whatever
/// its `cfg`.
pub fn mul_width_cap_in(source: &str) -> Result<u32, String> {
    const DECLARATION: &str = "const MAX_RECHECKABLE_MUL_WIDTH";
    let declarations: Vec<&str> = source
        .lines()
        .filter(|l| !l.trim_start().starts_with("//"))
        .filter(|l| {
            l.match_indices(DECLARATION).any(|(at, _)| {
                l[at + DECLARATION.len()..].starts_with(|c: char| c == ':' || c.is_whitespace())
            })
        })
        .collect();
    let line = match declarations.as_slice() {
        [line] => *line,
        [] => {
            return Err(
                "MAX_RECHECKABLE_MUL_WIDTH must still exist: if the tractability guard was \
                 removed, the wide-Mul kernel grade is being claimed on an inspection-level \
                 assumption — see tests/ay_blast_correspondence_gate.rs's header"
                    .to_string(),
            );
        }
        several => {
            return Err(format!(
                "MAX_RECHECKABLE_MUL_WIDTH is declared {} times; the coupling reads the cap as \
                 text and cannot tell which declaration the bridge compiles with, so keep exactly \
                 one: {several:?}",
                several.len()
            ));
        }
    };
    // The literal between `=` and `;`, so a trailing comment's digits are not
    // read as part of the value.
    let literal = line
        .split_once('=')
        .and_then(|(_, rest)| rest.split_once(';'))
        .map(|(value, _)| value.trim())
        .ok_or_else(|| format!("the cap has no `= <literal>;` initialiser: {line:?}"))?;
    let digits = literal.strip_suffix("u32").unwrap_or(literal).replace('_', "");
    digits.parse().map_err(|e| format!("unparsable cap {literal:?} in {line:?}: {e}"))
}

/// [`mul_width_cap_in`] over [`MUL_WIDTH_CAP_SOURCE`]; panics when the file or
/// the constant cannot be read.
#[must_use]
pub fn declared_mul_width_cap() -> u32 {
    let src = repo_path(MUL_WIDTH_CAP_SOURCE);
    let text = std::fs::read_to_string(&src)
        .unwrap_or_else(|e| panic!("must read {}: {e}", src.display()));
    mul_width_cap_in(&text).unwrap_or_else(|why| panic!("{}: {why}", src.display()))
}

/// The coupling between the ay-blast proof state and the multiply cap, or
/// `None` when code and proofs agree. `proves(name)` answers whether `name` is
/// a real, axiom-free theorem of the G16 file.
///
/// The bridge is decomposed into TWO obligations of different kind:
///   1. [`DISCHARGE_THEOREM`] — ay's Rust emits `mul_ay` (inspection;
///      un-closable inside clean, but a line-by-line structural comparison);
///   2. [`MODEL_MATCH_THEOREM`] — `mul_ay = mul_m` (pure mathematics, proved).
///
/// The cap may be lifted only when BOTH are discharged. So: obligation 2
/// regressing is a violation; both discharged is a violation too, deliberately,
/// marking the transition with instructions; otherwise the cap must equal
/// [`EXPECTED_MUL_WIDTH_CAP`].
#[must_use]
pub fn mul_width_coupling_violation(proves: impl Fn(&str) -> bool, cap: u32) -> Option<String> {
    let rust_gap_closed = proves(DISCHARGE_THEOREM);
    let model_gap_closed = proves(MODEL_MATCH_THEOREM);
    if !model_gap_closed {
        return Some(format!(
            "{MODEL_MATCH_THEOREM} must be a real, axiom-free Theorem — obligation 2 \
             (mul_ay = mul_m) was DISCHARGED and must not regress: it is the only half of the \
             correspondence clean can prove, so losing it silently returns the bridge to a \
             two-obligation state"
        ));
    }
    if rust_gap_closed {
        return Some(format!(
            "BOTH bridge obligations are now discharged ({DISCHARGE_THEOREM} and \
             {MODEL_MATCH_THEOREM}) — the ay-blast correspondence is complete.\n\
             This check is deliberately failing to mark the transition, not because anything is \
             broken. Next steps:\n\
               1. a wide `Mul` may now cite the structured theorem instead of re-checking a \
                per-instance SAT refutation, so MAX_RECHECKABLE_MUL_WIDTH (currently {cap}) can \
                be raised or removed;\n\
               2. rewrite this coupling (crates/trust-integration-tests/src/\
                clean_proof_obligations.rs) to assert the NEW state (correspondence proved, cap \
                lifted) rather than the gap;\n\
               3. update the honesty notes in g16_multiplier_equivalence.lean, \
                i128_mul_corner_bounds.lean and structured_multiplier_proof_gate.rs, which all \
                record wide `Mul` as [VALIDATED] pending exactly this."
        ));
    }
    (cap != EXPECTED_MUL_WIDTH_CAP).then(|| {
        format!(
            "MAX_RECHECKABLE_MUL_WIDTH is {cap}, expected {EXPECTED_MUL_WIDTH_CAP}, while the \
             bridge is INCOMPLETE ({DISCHARGE_THEOREM} is unproved).\n\
             The cap and the open obligation are the same fact: without a proof that ay's blast \
             IS the model's multiplier, a wide `Mul` re-check has no structured theorem to cite, \
             and the per-instance SAT refutation is intractable (~16x steps per +2 bits; ~2.0M \
             at width 8). Raising the cap here would claim a kernel grade on an \
             inspection-level assumption. If you intend to lift it, discharge the \
             correspondence first and name the proof {DISCHARGE_THEOREM}."
        )
    })
}

#[cfg(test)]
mod tests {
    use trust_certify::clean_island::{CleanIslandOutcome, CleanIslandSession, island_source_name};

    use super::*;

    /// One source checked in a fresh strict session, kept so its registered
    /// declarations can be audited afterwards.
    struct Checked {
        session: CleanIslandSession,
        outcome: CleanIslandOutcome,
    }

    impl Checked {
        fn source(source: &str) -> Self {
            let mut session = CleanIslandSession::new();
            let outcome = session.check(source);
            Self { session, outcome }
        }

        /// Check a proof file; it must be accepted as a whole.
        fn file(relative: &str) -> Self {
            let path = repo_path(relative);
            let source = std::fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
            let checked = Self::source(&source);
            assert!(
                !checked.outcome.is_rejected(),
                "{relative} no longer kernel-checks in process:\n{}",
                checked
                    .outcome
                    .errors
                    .iter()
                    .map(|err| format!("    {}", err.message))
                    .collect::<Vec<_>>()
                    .join("\n")
            );
            checked
        }

        /// Why `name` is not a real, axiom-free theorem of this source, or
        /// `Ok` when it is. A prelude theorem of the same name does not count:
        /// the source itself must register it.
        fn proves(&self, name: &str) -> Result<(), String> {
            if !self.outcome.registered.iter().any(|registered| registered == name) {
                return Err("the source registers no declaration of that name".to_string());
            }
            self.session.audit_cited_theorem(name).map_err(|verdict| format!("{verdict:?}"))
        }

        /// Every required name that [`Self::proves`] refuses, with the reason.
        fn unproved(&self, required: &[&str]) -> Vec<String> {
            required
                .iter()
                .filter_map(|name| self.proves(name).err().map(|why| format!("{name}: {why}")))
                .collect()
        }

        /// Every pin whose constant no longer has the pinned statement (or
        /// body), with both terms. Elaborates the pins into this session, so
        /// it runs after every [`Self::proves`]: a rejected pin source taints
        /// the session, and a tainted session proves nothing.
        fn unpinned(&mut self, pins: &[StatementPin]) -> Vec<String> {
            let outcome = self.session.check(&statement_pin_source(pins));
            if outcome.is_rejected() {
                return vec![format!(
                    "the pinned terms no longer elaborate:\n    {}",
                    outcome
                        .errors
                        .iter()
                        .map(|err| err.message.clone())
                        .collect::<Vec<_>>()
                        .join("\n    ")
                )];
            }
            let Some(env) = self.session.environment() else {
                return vec!["the session is tainted".to_string()];
            };
            let name = |spelling: &str| {
                island_source_name(spelling).unwrap_or_else(|e| panic!("{spelling}: {e}"))
            };
            pins.iter()
                .enumerate()
                .filter_map(|(i, pin)| {
                    let pin_name = statement_pin_name(pins, i);
                    let Some(pinned) =
                        env.get_const(&name(&pin_name)).and_then(|c| c.value.as_ref())
                    else {
                        return Some(format!(
                            "{}: pin {pin_name} was not registered",
                            pin.constant
                        ));
                    };
                    let Some(info) = env.get_const(&name(pin.constant)) else {
                        return Some(format!("{}: not in the environment", pin.constant));
                    };
                    let (what, actual) = match pin.part {
                        PinnedPart::Statement => ("statement", Some(&info.type_)),
                        PinnedPart::Definition => ("body", info.value.as_ref()),
                    };
                    match actual {
                        Some(actual) if actual == pinned => None,
                        Some(actual) => Some(format!(
                            "{}: its {what} is\n      {actual}\n    the pin is\n      {pinned}",
                            pin.constant
                        )),
                        None => Some(format!("{}: has no {what}", pin.constant)),
                    }
                })
                .collect()
        }
    }

    fn assert_pinned(file: &str, checked: &mut Checked, pins: &[StatementPin]) {
        let unpinned = checked.unpinned(pins);
        assert!(
            unpinned.is_empty(),
            "{file}: {} of {} pinned statements changed; a required theorem restated under the \
             same name is not the theorem the gates require. If the change is intended, update \
             the pin in crates/trust-integration-tests/src/clean_proof_obligations.rs with it:\n  {}",
            unpinned.len(),
            pins.len(),
            unpinned.join("\n  ")
        );
    }

    #[test]
    fn g16_multiplier_proves_its_theorems_and_the_mul_cap_is_coupled_to_them() {
        let mut g16 = Checked::file(G16_MULTIPLIER_PROOF);
        for (what, required) in [
            ("headline", G16_HEADLINE_THEOREMS),
            ("reduction", G16_REDUCTION_THEOREMS),
            ("obligation-2", &[MODEL_MATCH_THEOREM][..]),
        ] {
            let unproved = g16.unproved(required);
            assert!(
                unproved.is_empty(),
                "{G16_MULTIPLIER_PROOF}: {} of {} {what} theorems are not real, axiom-free \
                 theorems of the file:\n  {}",
                unproved.len(),
                required.len(),
                unproved.join("\n  ")
            );
        }

        let cap = declared_mul_width_cap();
        if let Some(violation) = mul_width_coupling_violation(|name| g16.proves(name).is_ok(), cap)
        {
            panic!("{violation}");
        }

        assert_pinned(G16_MULTIPLIER_PROOF, &mut g16, G16_PINS);
    }

    #[test]
    fn corner_bounds_proves_the_law_the_i128_mul_suppression_rests_on() {
        let mut corner = Checked::file(CORNER_BOUNDS_PROOF);
        let unproved = corner.unproved(CORNER_BOUNDS_THEOREMS);
        assert!(
            unproved.is_empty(),
            "{CORNER_BOUNDS_PROOF}: these are not real, axiom-free theorems of the file, and \
             trust-vcgen's v2_signed_mul_provably_cannot_overflow suppresses i128 Mul overflow \
             obligations on their strength:\n  {}",
            unproved.join("\n  ")
        );
        assert_pinned(CORNER_BOUNDS_PROOF, &mut corner, CORNER_BOUNDS_PINS);
    }

    /// Every theorem whose meaning a consumer relies on has its statement
    /// pinned: each corner-bounds theorem, each G16 headline theorem and
    /// obligation 2. A name added to one of those lists without a pin fails.
    #[test]
    fn every_load_bearing_theorem_has_a_pinned_statement() {
        let pinned = |pins: &[StatementPin], name: &str| {
            pins.iter().any(|pin| pin.constant == name && pin.part == PinnedPart::Statement)
        };
        let missing: Vec<&str> = CORNER_BOUNDS_THEOREMS
            .iter()
            .filter(|name| !pinned(CORNER_BOUNDS_PINS, name))
            .chain(
                G16_HEADLINE_THEOREMS
                    .iter()
                    .chain([MODEL_MATCH_THEOREM].iter())
                    .filter(|name| !pinned(G16_PINS, name)),
            )
            .copied()
            .collect();
        assert!(missing.is_empty(), "required theorems without a pinned statement: {missing:?}");
        // A pin names a constant of its own file, so it is checked against it.
        for (pins, prefix) in [(G16_PINS, "G16Mul."), (CORNER_BOUNDS_PINS, "CornerBox.")] {
            for pin in pins {
                assert!(
                    pin.constant.starts_with(prefix),
                    "{} pinned against the wrong file",
                    pin.constant
                );
            }
        }
    }

    /// RED CONTROL for the pins: a required theorem restated under its own
    /// name passes every name check (registered, a `theorem`, axiom-free) and
    /// must still be refused. So must one restated as the value it computes
    /// to, which is the same proposition to the kernel: the pin is
    /// structural. The genuine statement, proved the file's way, passes. A
    /// pinned definition body is held the same way.
    #[test]
    fn a_required_theorem_restated_under_its_name_is_refused() {
        const NAME: &str = "CornerBox.corner_witness_negative";
        let pin: Vec<StatementPin> =
            CORNER_BOUNDS_PINS.iter().filter(|pin| pin.constant == NAME).copied().collect();
        assert_eq!(pin.len(), 1);
        for (restated, refused) in [
            ("True := True.intro", true),
            ("Eq Int (Int.negOfNat 6) (Int.negOfNat 6) := rfl", true),
            ("Eq Int (Int.mul (Int.negSucc 1) (Int.ofNat 3)) (Int.negOfNat 6) := rfl", false),
        ] {
            let mut checked = Checked::source(&format!(
                "namespace CornerBox\ntheorem corner_witness_negative : {restated}\nend CornerBox\n"
            ));
            assert!(!checked.outcome.is_rejected(), "{restated}: {:?}", checked.outcome.errors);
            assert_eq!(checked.proves(NAME), Ok(()), "{restated}: the name checks must pass");
            let unpinned = checked.unpinned(&pin);
            assert_eq!(!unpinned.is_empty(), refused, "{restated}: {unpinned:?}");
            if refused {
                assert!(unpinned[0].contains("its statement is"), "{unpinned:?}");
            }
        }

        // A pinned definition body likewise, and only up to bound-variable
        // names: renaming the binder is the same body, `True` is not.
        let body = [StatementPin {
            constant: "CornerBox.Law",
            part: PinnedPart::Definition,
            ty: "Prop",
            term: "∀ (a : Int), Eq Int a a",
        }];
        for (restated, refused) in [("True", true), ("∀ (b : Int), Eq Int b b", false)] {
            let mut checked = Checked::source(&format!(
                "namespace CornerBox\ndef Law : Prop := {restated}\nend CornerBox\n"
            ));
            assert!(!checked.outcome.is_rejected(), "{restated}: {:?}", checked.outcome.errors);
            let unpinned = checked.unpinned(&body);
            assert_eq!(!unpinned.is_empty(), refused, "{restated}: {unpinned:?}");
            if refused {
                assert!(unpinned[0].contains("its body is"), "{unpinned:?}");
            }
        }
    }

    /// RED CONTROL for "axiom-free": a theorem that leans on an axiom is refused
    /// on its OWN account (its strict certification audit names the axiom), not
    /// only because the axiom declaration beside it is refused, and it is not
    /// registered, so no required-name check can be satisfied by it.
    #[test]
    fn a_theorem_leaning_on_an_axiom_is_rejected_and_unregistered() {
        let leaning =
            Checked::source("axiom bad : False\ntheorem leans : (0 : Nat) = 1 := False.elim bad\n");
        assert!(leaning.outcome.is_rejected(), "an axiom-backed island was accepted");
        assert!(
            leaning.outcome.errors.iter().any(|err| err.message.contains("`leans`")
                && err.message.contains("strict certification audit")
                && err.message.contains("bad")),
            "the theorem itself must be refused by its strict audit, naming the axiom, not only \
             the axiom declaration: {:?}",
            leaning.outcome.errors
        );
        assert!(leaning.proves("leans").is_err(), "an axiom-backed theorem passed proves()");
        assert!(
            !leaning.outcome.registered.iter().any(|name| name == "leans" || name == "bad"),
            "{:?}",
            leaning.outcome.registered
        );
    }

    /// RED CONTROL for "a real theorem": registration alone is not enough. A
    /// `def` wearing a required name registers, and must still be refused; so
    /// must a name the source never declares.
    #[test]
    fn a_definition_or_an_absent_name_is_not_a_proof() {
        let def = Checked::source("def mul_box_upper : Nat := 0\n");
        assert!(!def.outcome.is_rejected(), "{:?}", def.outcome.errors);
        assert!(def.outcome.registered.iter().any(|name| name == "mul_box_upper"));
        let why = def.proves("mul_box_upper").expect_err("a def is not a theorem");
        assert!(why.contains("DeclarationNotTheorem"), "{why}");
        assert!(def.proves("mul_box_lower").is_err(), "an absent name passed proves()");

        let theorem = Checked::source("theorem mul_box_upper : (1 : Nat) = 1 := rfl\n");
        assert_eq!(theorem.proves("mul_box_upper"), Ok(()));
    }

    #[test]
    fn the_mul_width_coupling_refuses_every_drift() {
        let state = |proved: &'static [&'static str]| move |name: &str| proved.contains(&name);
        // Today: obligation 2 closed, obligation 1 open, cap 8.
        assert_eq!(mul_width_coupling_violation(state(&[MODEL_MATCH_THEOREM]), 8), None);
        // The cap raised (or lowered) while obligation 1 is open.
        for cap in [0, 7, 9, 64] {
            let why = mul_width_coupling_violation(state(&[MODEL_MATCH_THEOREM]), cap)
                .unwrap_or_else(|| panic!("cap {cap} accepted"));
            assert!(why.contains(&format!("MAX_RECHECKABLE_MUL_WIDTH is {cap}")), "{why}");
        }
        // Obligation 2 regressed, whatever the cap.
        for cap in [8, 9] {
            let why = mul_width_coupling_violation(state(&[]), cap)
                .unwrap_or_else(|| panic!("a regressed obligation 2 accepted at cap {cap}"));
            assert!(why.contains("must not regress"), "{why}");
        }
        // Both discharged: the transition is marked, never passed silently.
        let why = mul_width_coupling_violation(state(&[MODEL_MATCH_THEOREM, DISCHARGE_THEOREM]), 8)
            .expect("the transition must fail");
        assert!(why.contains("BOTH bridge obligations"), "{why}");
    }

    #[test]
    fn the_cap_is_read_from_the_bridge_declaration() {
        assert_eq!(mul_width_cap_in("const MAX_RECHECKABLE_MUL_WIDTH: u32 = 8;\n"), Ok(8));
        assert_eq!(
            mul_width_cap_in(
                "// x\npub(crate) const MAX_RECHECKABLE_MUL_WIDTH: u32 = 16; // was 4\n"
            ),
            Ok(16)
        );
        assert_eq!(mul_width_cap_in("const MAX_RECHECKABLE_MUL_WIDTH: u32 = 1_6u32;\n"), Ok(16));
        assert!(mul_width_cap_in("const OTHER: u32 = 8;\n").is_err());
        assert!(mul_width_cap_in("const MAX_RECHECKABLE_MUL_WIDTH: u32;\n").is_err());
        assert!(mul_width_cap_in("const MAX_RECHECKABLE_MUL_WIDTH: u32 = WIDTH;\n").is_err());
        // A comment naming the constant is not a declaration, and neither is a
        // longer name that starts with it.
        assert_eq!(
            mul_width_cap_in(
                "/// see `const MAX_RECHECKABLE_MUL_WIDTH`\n\
                 const MAX_RECHECKABLE_MUL_WIDTH_LIMIT: u32 = 64;\n\
                 const MAX_RECHECKABLE_MUL_WIDTH: u32 = 8;\n"
            ),
            Ok(8)
        );
        // A cfg-split pair: which one the bridge compiles with is not text.
        let why = mul_width_cap_in(
            "#[cfg(test)]\nconst MAX_RECHECKABLE_MUL_WIDTH: u32 = 8;\n\
             #[cfg(not(test))]\nconst MAX_RECHECKABLE_MUL_WIDTH: u32 = 64;\n",
        )
        .expect_err("two declarations must be refused");
        assert!(why.contains("declared 2 times"), "{why}");
    }
}
