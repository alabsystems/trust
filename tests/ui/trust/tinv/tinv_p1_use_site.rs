//@ revisions: on off json certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ [on] build-pass
//@ [off] build-pass
//@ [json] build-pass
//@ [certify] check-fail
//@ [certify] dont-require-annotations: ERROR
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ [on] compile-flags: -Ztrust-tinv
//@ [certify] compile-flags: -Ztrust-tinv -Ztrust-policy=certify
//@ [json] compile-flags: -Ztrust-tinv -Ztrust-verify-output=json --error-format=human
//@ [off] forbid-output: [certificate: this crate's TINV Houdini induction
//@ [off] forbid-output: proved UNDER this crate's certified type invariant
//! TINV steps 10.5 and 10.7 end to end on REAL MIR (the `a3d_wire::json::Parser` shape,
//! design §5 P1): under `-Ztrust-tinv` the pre-pass certifies `i <= len(b)` for `P`
//! (`tinv_p1_json_parser` pins that), step 10.5 installs `Arc::clone` of the STORED use set
//! into the callee-summary context, and `rest`'s slice row `&self.b[self.i..]`, which
//! needs the invariant (`i <= len(b)` at entry of `&self`), proves as
//! `TypeInvariantComposed` — `Trusted`, never `Certified` — with its premise rendered on
//! the terminal note (`on`: the headline and the `assumes type_invariant(..)#2` line, both
//! NOTE-annotated on `rest`, spelled so the `off` forbid patterns do not match the
//! annotations when `rest`'s source is rendered) and on the JSON transport row (`json`).
//! Under `-Ztrust-policy=certify` (`certify`) the premise is FATAL for `rest` (TINV-29),
//! as an instance hypothesis is. Without the flag (`off`) nothing is installed: the same row FAILS, and no premise,
//! certificate line or note is printed.
//!
//! MEASURED 2026-10-10 (stage 1 of `tinv/step10-install` over origin/main `912bbdf300`,
//! steps 10.7 + 10.5 + 10.6 stacked), per function, flag off -> on: `rest` 1 failed -> 1 proved (`TypeInvariantComposed`);
//! `bump` unchanged (1 proved, 1 failed, 1 runtime-checked: `self.i += 1` after
//! `self.peek()?` needs `peek`'s `Some`-arm lemma, which a use site never reads, design §6
//! item 2); `literal` 1 proved, 2 failed, 1 unknown -> 0 proved, 2 failed, 1 unknown,
//! 1 runtime-checked: a use-site fact was conjoined into its rows, so the TINV-26 cap
//! strips the native full verifier's proof of an `overflow:add` row (the native lanes solve
//! a formula that need not carry the tag) — the designed precision cost of a premised
//! body; `parse` unchanged.
#![forbid(unsafe_code)]

struct P<'a> {
    b: &'a [u8],
    i: usize,
}

impl<'a> P<'a> {
    fn peek(&self) -> Option<u8> {
        self.b.get(self.i).copied()
    }

    fn bump(&mut self) -> Option<u8> {
        let c = self.peek()?;
        self.i += 1;
        Some(c)
    }

    fn rest(&self) -> &'a [u8] {
        //[on]~^ NOTE 1 obligation(s) were proved UNDER this crate's
        //[certify]~^^ ERROR Trust certify verification failed for `tinv_p1_use_site::P::<'_>::rest`: its rows carry a type-invariant premise
        //[on]~| NOTE assumes type_invariant(tinv_p1_use_site::P)#2 `i <= len(b)` [certificate:
        &self.b[self.i..]
    }

    fn literal(&mut self, w: &'static [u8]) -> bool {
        if self.b.len() >= self.i + w.len() && &self.b[self.i..self.i + w.len()] == w {
            self.i += w.len();
            true
        } else {
            false
        }
    }
}

pub fn parse(b: &[u8]) -> usize {
    let mut p = P { b, i: 0 };
    p.bump();
    let _ = p.literal(b"null");
    p.rest().len()
}

// The JSON transport row of `rest` carries the premise verbatim (`assumes`, step 10.7).
//[json]~? RAW "assumes":["assumes type_invariant(tinv_p1_use_site::P)#2 `i <= len(b)` [certificate: this crate's TINV Houdini induction,
