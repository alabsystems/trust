// Trust (wave-EP REVIEW, 2026-08-17) — ADVERSARIAL CORPUS B of three: the FIVE `flip.rs`
// ADMISSIONS, attacked directly.
//
// Every shape here exists to make `payload_borrow_temps` say YES about a local whose use is NOT
// the single deref-read its doc-comment promises. The claim under attack, verbatim:
//
//   "TOTAL value-mentions == 2 (the def dest + the one use) ... That clause is the airtight
//    single-use guarantee: a temp stored, re-borrowed, copied or used again appears a third time
//    and is rejected, so no interior pointer can escape or alias beyond the one read."
//
// MEASURED VERDICT: no attack got through. Escape-by-return and escape-into-a-call both leave
// `deref_read == 0`; read-twice and reborrow both push mentions past 2; every non-scalar,
// non-shared-ref, non-arg or nested-payload base fails the def clause.
//
// BUT the clause is airtight only in conjunction with a check elsewhere in `gate_derived_body`:
// `MentionCounter` skips `PlaceContext::NonUse`, which covers `AscribeUserTy` as well as the two
// storage markers, and what makes the count total is the statement allow-list's fail-closed
// `other => return Err("statement outside fragment")` — so an admitted body can only carry
// `Assign`/`StorageLive`/`StorageDead`. State that where the clause is claimed.
//
// AND the clause is UNWITNESSED: a driver with `mentions == 2` deleted moves NOTHING across
// 13,774 clean-kernel bodies at both levels, 1,588 probe-union bodies and these 115 (0 rows
// changed, 0 flips gained or lost). It is necessary in principle — without it
// `_t = &(((*_p) as V).k); _x = copy (*_t); g(move _t)` is admitted and `operand_ok` passes the
// bare `move _t` through `place_ok`'s zero-projection arm — but its correctness is carried by
// review, not by measurement.
//
// ONE ROW MOVED THAT THE WAVE DID NOT PRICE: `E::reborrow` below takes admitted-and-wrong 0 -> 1.

#![allow(dead_code)]

#[derive(Clone, Copy)]
pub enum E {
    V(u32),
    N,
}

#[derive(Clone, Copy)]
pub enum E2 {
    A(u32),
    B(u32),
    C,
}

// ---------------------------------------------------------------------------------------------
// B1..B4 — THE BORROW ESCAPES. If the arm-binding borrow can leave the body, `mentions == 2` is
// not the airtight clause it claims. Each of these is a body where built's arm binding is the
// SAME `&u32` and the consumer is something other than one deref-read.
// ---------------------------------------------------------------------------------------------

impl E {
    /// B1 — THE BORROW IS RETURNED. Built's arm binding is exactly `_3 = &(((*_1) as V).0)` and
    /// the consumer is `_0 = copy _3` — a BARE local use, not a deref-read. If the shim minted a
    /// payload temp here and `payload_borrow_temps` admitted it, the interior pointer would leave
    /// the body with the gate's blessing. It must not.
    pub fn escape_return(&self) -> &u32 {
        match self {
            E::V(h) => h,
            _ => &0,
        }
    }

    /// B2 — THE BORROW IS PASSED TO A CALL. `g(move _t)` is `interior_arg_temps`' use kind, not
    /// this one. If the two sets ever merge, this is the body that shows it.
    pub fn escape_call(&self) -> u32 {
        match self {
            E::V(h) => sink(h),
            _ => 0,
        }
    }

    /// B3 — THE PAYLOAD IS READ TWICE THROUGH ONE BINDING. Three mentions; must be refused.
    pub fn read_twice(&self) -> u32 {
        match self {
            E::V(h) => *h + *h,
            _ => 0,
        }
    }

    /// B4 — THE BORROW IS REBORROWED. `&*h` is a second borrow off the same temp.
    pub fn reborrow(&self) -> u32 {
        match self {
            E::V(h) => *(&*h),
            _ => 0,
        }
    }
}

#[inline(never)]
pub fn sink(x: &u32) -> u32 {
    *x
}

// ---------------------------------------------------------------------------------------------
// B5..B8 — THE `func.scopes` FIREWALL. The plan consults it FIRST. Each of these opens a lexical
// scope in the arm, which is exactly what the firewall is supposed to refuse.
// ---------------------------------------------------------------------------------------------

impl E {
    /// B5 — a `let` inside the payload arm.
    pub fn scoped_let(&self) -> u32 {
        match self {
            E::V(h) => {
                let t = *h;
                t
            }
            _ => 0,
        }
    }
    /// B6 — a `let` binding the WHOLE match, so the scope is outside the arm.
    pub fn scoped_outer(&self) -> u32 {
        let r = match self {
            E::V(h) => *h,
            _ => 0,
        };
        r
    }
    /// B7 — a `let` in the CONST arm only.
    pub fn scoped_const_arm(&self) -> u32 {
        match self {
            E::V(h) => *h,
            _ => {
                let z = 0;
                z
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------
// B9..B13 — THE JOIN. The plan requires "one parameter, immediately returned". Each of these
// makes the join compute, which the plan says it has not measured.
// ---------------------------------------------------------------------------------------------

impl E {
    /// B9 — the join adds one.
    pub fn join_computes(&self) -> u32 {
        (match self {
            E::V(h) => *h,
            _ => 0,
        }) + 1
    }
    /// B10 — the join casts.
    pub fn join_casts(&self) -> u64 {
        (match self {
            E::V(h) => *h,
            _ => 0,
        }) as u64
    }
    /// B11 — the join compares.
    pub fn join_compares(&self) -> bool {
        (match self {
            E::V(h) => *h,
            _ => 0,
        }) == 3
    }
}

// ---------------------------------------------------------------------------------------------
// B14..B18 — THE ARM COMPUTES. The plan requires the triple to be at index 0 of its block and its
// result to be the SOLE `Br` argument.
// ---------------------------------------------------------------------------------------------

impl E {
    /// B14 — arithmetic after the read, inside the arm.
    pub fn arm_adds(&self) -> u32 {
        match self {
            E::V(h) => *h + 1,
            _ => 0,
        }
    }
    /// B15 — a cast inside the arm.
    pub fn arm_casts(&self) -> u64 {
        match self {
            E::V(h) => *h as u64,
            _ => 0,
        }
    }
    /// B16 — the CONST arm is not a folded constant but an arithmetic expression.
    pub fn const_arm_computes(&self, k: u32) -> u32 {
        match self {
            E::V(h) => *h,
            _ => k + 1,
        }
    }
    /// B17 — the const arm forwards a PARAM (no `Const` instruction at all).
    pub fn const_arm_param(&self, k: u32) -> u32 {
        match self {
            E::V(h) => *h,
            _ => k,
        }
    }
}

// ---------------------------------------------------------------------------------------------
// B19..B23 — THE RECEIVER. `is_ref_enum_payload_read` pins the base to a SHARED-ref ARG whose
// pointee is an enum. Each of these moves the base off that pin.
// ---------------------------------------------------------------------------------------------

impl E {
    /// B19 — `&mut self`. `m.is_not()` must refuse it.
    pub fn mut_recv(&mut self) -> u32 {
        match self {
            E::V(h) => *h,
            _ => 0,
        }
    }
    /// B20 — BY VALUE. No `gep`, no borrow, no marker — the pre-wave by-value payload arm.
    pub fn by_value(self) -> u32 {
        match self {
            E::V(h) => h,
            _ => 0,
        }
    }
    /// B21 — a plain `&E` PARAMETER rather than `&self` (same MIR, different HIR).
    pub fn as_param(e: &E) -> u32 {
        match e {
            E::V(h) => *h,
            _ => 0,
        }
    }
    /// B22 — a DOUBLE reference `&&E`. The base is `&&E`, not `&E`; the projection is four levels.
    pub fn double_ref(e: &&E) -> u32 {
        match *e {
            E::V(ref h) => *h,
            _ => 0,
        }
    }
    /// B23 — the enum reached through a STRUCT field, not the arg directly.
    pub fn via_field(s: &Holder) -> u32 {
        match &s.e {
            E::V(h) => *h,
            _ => 0,
        }
    }
}

pub struct Holder {
    pub e: E,
}

// ---------------------------------------------------------------------------------------------
// B24..B28 — NON-SCALAR AND REFERENCE PAYLOADS. `scalar_ok` on the field type is what keeps the
// `&FieldTy` temp inside the fragment. Each of these has a payload the fragment must refuse.
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Copy)]
pub struct Pair(pub u32, pub u32);

#[derive(Clone, Copy)]
pub enum StructPay {
    V(Pair),
    N,
}
impl StructPay {
    /// B24 — the payload is a STRUCT; `&Pair` is outside the scalar denotation.
    pub fn whole(&self) -> Pair {
        match self {
            StructPay::V(p) => *p,
            _ => Pair(0, 0),
        }
    }
    /// B25 — the payload is a struct and the arm reads a FIELD of it: a FOUR-level projection
    /// `[Deref, Downcast, Field, Field]`, one past everything `place_ok` and
    /// `is_ref_enum_payload_read` carry.
    pub fn nested_field(&self) -> u32 {
        match self {
            StructPay::V(p) => p.0,
            _ => 0,
        }
    }
}

pub enum RefPay<'a> {
    V(&'a u32),
    N,
}
impl RefPay<'_> {
    /// B26 — THE PAYLOAD IS ITSELF A REFERENCE. Built's arm binding is `&&u32`; the read through
    /// it is a double deref. `scalar_ok(&u32)` is false, so the borrow-def clause must refuse.
    pub fn deref_payload(&self) -> u32 {
        match self {
            RefPay::V(r) => **r,
            _ => 0,
        }
    }
    /// B27 — the payload reference is RETURNED, so the inner borrow escapes too.
    pub fn escape_inner(&self) -> &u32 {
        match self {
            RefPay::V(r) => r,
            _ => &0,
        }
    }
}

#[derive(Clone, Copy)]
pub enum TuplePay {
    V((u32, bool)),
    N,
}
impl TuplePay {
    /// B28 — a TUPLE payload. `&(u32, bool)` is outside `scalar_ok`.
    pub fn t(&self) -> u32 {
        match self {
            TuplePay::V(t) => t.0,
            _ => 0,
        }
    }
}

// ---------------------------------------------------------------------------------------------
// B29..B33 — NESTED ENUM PAYLOADS. A payload that is itself an enum makes the `Downcast` chain
// two deep, which is the shape the wave's projection-length clauses (`len() == 3`) exclude.
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Copy)]
pub enum Inner {
    I(u32),
    J,
}

#[derive(Clone, Copy)]
pub enum Outer {
    O(Inner),
    P,
}

impl Outer {
    /// B29 — nested match, both levels by ref. Two payload triples, five blocks.
    pub fn nested(&self) -> u32 {
        match self {
            Outer::O(i) => match i {
                Inner::I(x) => *x,
                _ => 1,
            },
            _ => 0,
        }
    }
    /// B30 — the inner enum is bound and returned whole.
    pub fn inner_whole(&self) -> Inner {
        match self {
            Outer::O(i) => *i,
            _ => Inner::J,
        }
    }
}

// ---------------------------------------------------------------------------------------------
// B34..B38 — GENERIC / LIBRARY ENUMS. `Option`/`Result` are the enums real code matches, and
// their niche layouts make the `gep` offset a different number from the shipped pair's.
// ---------------------------------------------------------------------------------------------

pub fn opt_u32(o: &Option<u32>) -> u32 {
    match o {
        Some(x) => *x,
        None => 0,
    }
}

pub fn opt_bool(o: &Option<bool>) -> bool {
    match o {
        Some(x) => *x,
        None => false,
    }
}

pub fn res_both(r: &Result<u32, u32>) -> u32 {
    match r {
        Ok(x) => *x,
        Err(y) => *y,
    }
}

pub fn res_one(r: &Result<u32, u32>) -> u32 {
    match r {
        Ok(x) => *x,
        Err(_) => 0,
    }
}

/// B38 — `Option<&u32>`: the payload is a reference AND the enum is niche-optimized.
pub fn opt_ref(o: &Option<&u32>) -> u32 {
    match o {
        Some(x) => **x,
        None => 0,
    }
}
