// LANE SC — the STATEMENT-CALL SEQUENCE tranche: `{ self.a(); self.b(); ... }`, N result-less
// unit statements in one block, which the trust-ir spells as ONE block of N `call @f(%0)` nodes
// and a bare `ret`.
//
// The corpus bodies are `env::Environment::ensure_native_reducers` (21 calls) and
// `env::native_reducers_bitvec::<impl Environment>::init_bitvec_native_reducers` (4 calls).
// The N == 1 form is lane S1F's `unit_stmt` class and ALREADY FLIPS (five bodies:
// `init_arith_native_reducers`, `init_native_reducers`, `init_quot`,
// `materialize_extension_states`, `pop_binder_local`), so `n1_*` here is the CONTROL that must
// not move.
#![allow(dead_code, clippy::all)]

pub struct Env {
    n: u64,
}

impl Env {
    #[inline(never)]
    pub fn s1(&mut self) {
        self.n += 1;
    }
    #[inline(never)]
    pub fn s2(&mut self) {
        self.n += 2;
    }
    #[inline(never)]
    pub fn s3(&mut self) {
        self.n += 3;
    }
    #[inline(never)]
    pub fn s4(&mut self) {
        self.n += 4;
    }
    #[inline(never)]
    pub fn r1(&self) {
        let _ = self.n;
    }
    #[inline(never)]
    pub fn r2(&self) {
        let _ = self.n;
    }

    // THE CONTROL — N == 1, lane S1F's unit-statement class, already flipping.
    pub fn n1_mut(&mut self) {
        self.s1();
    }
    pub fn n1_shared(&self) {
        self.r1();
    }

    // THE SUBJECT — N >= 2.
    pub fn n2_mut(&mut self) {
        self.s1();
        self.s2();
    }
    pub fn n2_shared(&self) {
        self.r1();
        self.r2();
    }
    pub fn n3_mut(&mut self) {
        self.s1();
        self.s2();
        self.s3();
    }
    // the `init_bitvec_native_reducers` arity, verbatim
    pub fn n4_mut(&mut self) {
        self.s1();
        self.s2();
        self.s3();
        self.s4();
    }

    // A free-function spelling of the same sequence (the receiver is argument 0 either way).
    pub fn n2_free(&mut self) {
        Env::s1(self);
        Env::s2(self);
    }
}

// A sequence over a SECOND parameter — two distinct argument values, so the per-call argument
// slot cannot be keyed by the value alone.
pub struct Two {
    a: Env,
}
#[inline(never)]
pub fn g1(e: &Env) {
    let _ = e.n;
}
#[inline(never)]
pub fn g2(e: &Env, f: &Env) {
    let _ = e.n + f.n;
}
impl Two {
    pub fn n2_twoargs(&self, other: &Env) {
        g2(&self.a, other);
        g1(other);
    }
}

// NEAR MISSES that must stay refused.
impl Env {
    // a TAIL expression after the statements — the last call's value is returned
    pub fn x1_tail(&mut self) -> u64 {
        self.s1();
        self.n
    }
    // a `let` — the wave-MF scope firewall
    pub fn x2_let(&mut self) {
        let k = 1u64;
        self.s1();
        self.n += k;
    }
    // a call that DECLARES a result
    #[inline(never)]
    pub fn q(&self) -> u64 {
        self.n
    }
    pub fn x3_result(&self) {
        let _ = self.q();
        self.r1();
    }
}

// A sequence with a SECOND, BY-VALUE SCALAR argument — the shape whose slot the type component
// can discriminate (`&mut Env` is opaque on both sides; `u64` is a scalar on both).
impl Env {
    #[inline(never)]
    pub fn t1(&mut self, k: u64) {
        self.n += k;
    }
    #[inline(never)]
    pub fn t2(&mut self, k: u64) {
        self.n -= k;
    }
    pub fn n2_scalar(&mut self, k: u64) {
        self.t1(k);
        self.t2(k);
    }
}

// A sequence over TWO DISTINCT bare reference parameters.
#[inline(never)]
pub fn h1(a: &Env, b: &Env) {
    let _ = a.n + b.n;
}
#[inline(never)]
pub fn h2(b: &Env, a: &Env) {
    let _ = a.n + b.n;
}
pub fn n2_distinct(a: &Env, b: &Env) {
    h1(a, b);
    h2(b, a);
}

// Groups of DIFFERENT arity in one sequence — the marker run length is per group, not per body.
pub fn n2_mixed_arity(a: &Env, b: &Env) {
    g2(a, b);
    g1(b);
}
