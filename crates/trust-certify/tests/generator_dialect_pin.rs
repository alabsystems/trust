// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or MIT

//! Generator-dialect pin: the pearlite→Clean generator (trust-wp
//! `tests/creusot_compat/pearlite_to_clean.py`) emits fully parenthesized
//! Clean over exactly these forms — `Int` arithmetic (`+ - * / %`, unary
//! `-`), Prop comparisons (`= ≠ < ≤ > ≥`), the connectives (`∧ ∨ ¬ →`), and
//! `True`/`False`. Every form must register in the REAL island environment;
//! a red here means the island prelude drifted out from under the generator
//! and ported corpora would start refusing at the kernel stage.

use trust_certify::clean_island::check_clean_island;

#[test]
fn generator_dialect_forms_register_in_the_island_environment() {
    let forms: &[(&str, &str)] = &[
        ("int_arith", "def sqr_spec (x : Int) : Int := (x * x)"),
        (
            "prop_le_conj",
            "def in_range (i : Int) (n : Int) : Prop := ((0 \u{2264} i) \u{2227} (i < n))",
        ),
        (
            "implication",
            "def imp_pin (a : Int) (b : Int) : Prop := ((a < b) \u{2192} (a \u{2264} b))",
        ),
        ("ne", "def ne_pin (a : Int) (b : Int) : Prop := (a \u{2260} b)"),
        ("unary_neg", "def neg_pin (x : Int) : Int := (- x)"),
        ("div_mod", "def dm_pin (x : Int) : Int := ((x / 2) + (x % 2))"),
        (
            "truth_not",
            "def truth_pin : Prop := (True \u{2227} (\u{00ac} False))",
        ),
        (
            "disjunction_ge_gt",
            "def disj_pin (a : Int) (b : Int) : Prop := ((a > b) \u{2228} (b \u{2265} a))",
        ),
        // v1.1 forms: the `let` semicolon spelling and `if/then/else` over
        // decidable Int comparisons (conjunctive + nested conditions).
        (
            "let_chain",
            "def let_pin (x : Int) : Int := (let y := (x + 1); (let z := (y * y); (z - 1)))",
        ),
        (
            "ite_cmp",
            "def abs_pin (x : Int) : Int := (if (x < 0) then (- x) else x)",
        ),
        (
            "ite_conj_nested",
            "def sign_pin (x : Int) (n : Int) : Int := (if ((0 \u{2264} x) \u{2227} (x < n)) then x else (if (x = 0) then 0 else 1))",
        ),
        (
            "let_of_ite",
            "def lite_pin (a : Int) (b : Int) : Int := (let m := (if (a < b) then a else b); (m + 1))",
        ),
        // v1.2 call forms: curried within-island application. The emitter
        // orders callee defs before callers in ONE island; forward and self
        // reference REJECT (soundness-probed), so cycles cannot emit.
        (
            "island_call",
            "def sq_pin (x : Int) : Int := (x * x)\n\ndef quad_pin (x : Int) : Int := ((sq_pin x) + (sq_pin x))",
        ),
        (
            "call_expr_args",
            "def h_pin (a : Int) (b : Int) : Int := (a + b)\n\ndef useh_pin (x : Int) : Int := (h_pin (x + 1) (x * 2))",
        ),
        (
            "prop_calls_int",
            "def dbl_pin (x : Int) : Int := (x * 2)\n\ndef even_pin (y : Int) (x : Int) : Prop := (y = (dbl_pin x))",
        ),
        // v1.3 quantifier forms: `forall i : Int,` and the `∃` spelling
        // (bare `exists` is NOT an island keyword — probed 2026-07-22).
        (
            "forall_int",
            "def allq_pin (n : Int) : Prop := (forall i : Int, ((0 \u{2264} i) \u{2192} (i \u{2264} (n + i))))",
        ),
        (
            "exists_unicode",
            "def wit_pin (n : Int) : Prop := (\u{2203} j : Int, (n = (j + j)))",
        ),
        (
            "nested_quantifiers",
            "def dense_pin : Prop := (forall i : Int, (\u{2203} j : Int, (i \u{2264} j)))",
        ),
        // §2 bounded-domain forms: machine binders encode as bounded-Int
        // quantification — ∀ guards by implication, ∃ constrains by
        // conjunction (the duality; collapsing it makes the witness bound
        // vacuous). The u64 form pins the widest literal.
        (
            "bounded_forall_impl",
            "def bfa_pin (n : Int) : Prop := (forall i : Int, (((0 \u{2264} i) \u{2227} (i < 4294967296)) \u{2192} ((i + n) = (n + i))))",
        ),
        (
            "bounded_exists_conj",
            "def bex_pin (n : Int) : Prop := (\u{2203} i : Int, (((0 \u{2264} i) \u{2227} (i < 256)) \u{2227} (n = (i + i))))",
        ),
        (
            "bounded_u64_literal",
            "def bwd_pin : Prop := (forall i : Int, (((0 \u{2264} i) \u{2227} (i < 18446744073709551616)) \u{2192} (i = i)))",
        ),
        // §3 vocabulary layer (owner-ruled OPEN 2026-07-23, Seq→List): the
        // pearlite sequence vocabulary as kernel-checked aliases over the
        // List theories the island environment already carries. Each future
        // table entry (view functions, further ops) lands with its own
        // battery; these three forms are the contracted base.
        (
            "seq_type_alias",
            "def SeqPin (a : Type) : Type := List a\n\ndef seq_alias_use (xs : SeqPin Int) : Prop := (xs = xs)",
        ),
        (
            "seq_len_int",
            "def seq_len_pin (xs : List Int) : Int := (Int.ofNat xs.length)",
        ),
        (
            "seq_index_get",
            "def seq_get_pin (xs : List Int) (i : Nat) : Prop := (xs.get? i = xs.get? i)",
        ),
        // §3 entry 4: membership — pearlite `xs.contains(x)` renders the
        // kernel's List.Mem Prop directly (Bool-eq spellings do not register).
        (
            "seq_contains_mem",
            "def seq_mem_pin (xs : List Int) (x : Int) : Prop := (List.Mem x xs)",
        ),
        // The machine-element bounding lane's foundation form: the
        // well-formedness predicate for a u64-element collection, expressed
        // entirely in already-pinned vocabulary (membership + the bounded
        // domain). The lane's translator/emitter entries land ONLY behind
        // batteries that conjoin exactly this predicate — an island def over
        // an unbounded List Int without it is a DIFFERENT definition.
        (
            "machine_element_bound",
            "def wf_u64_pin (xs : List Int) : Prop := (forall x : Int, ((List.Mem x xs) \u{2192} ((0 \u{2264} x) \u{2227} (x < 18446744073709551616))))",
        ),
    ];
    for (label, source) in forms {
        let outcome = check_clean_island(source);
        assert!(
            !outcome.is_rejected(),
            "generator dialect form `{label}` no longer registers: {:?}",
            outcome.errors
        );
        assert_eq!(
            outcome.registered.len(),
            source.matches("def ").count(),
            "generator dialect form `{label}` registered unexpectedly: {:?}",
            outcome.registered
        );
    }
}
