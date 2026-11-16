//@ revisions: on off
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ [on] compile-flags: -Ztrust-tinv
//@ [off] rustc-env:TRUST_TINV=1
//@ rustc-env:TRUST_TINV_NOTES=1
//@ [off] forbid-output: TINV:
//@ forbid-output: withheld by the escape census
//@ [on] forbid-output: withheld at G
//@ [on] forbid-output: (Situatedness)
//@ [off] forbid-output: certified:
//! TINV step 9 (design §5 P1, the json `Parser` reduction) on REAL MIR: under
//! `-Ztrust-tinv` the pre-pass selects `P` (every gate passes, the census denies
//! nothing), the untrusted synthesis proposes `i <= len(b)`, and Houdini runs with
//! `certify_vc` as the mint; `TRUST_TINV_NOTES=1` reports it. Without the flag
//! (`off`) nothing runs and nothing is reported, although `off` sets the retired
//! `TRUST_TINV=1` environment switch (step 10.0: the env read is gone; only the
//! tracked `-Ztrust-tinv` option enables the pre-pass).
//!
//! MEASURED 2026-10-06 (increment C): every conjunct dropped, `bump`'s Return edge
//! parts as `Situatedness` and its call-point row refuted.
//!
//! RE-MEASURED 2026-10-06 (TINV-18..20): every row of `i <= len(b)` is now SITUATED and
//! all but two are proved (`trust-vcgen/src/type_invariant/p1_realmir_tests.rs` pins
//! each row on this crate's own inventory). It still does not certify, and the `on`
//! rail now pins WHY: the first drop of `i <= len(b)` is `bump`'s Return edge part
//! from `bb7` (`self.i += 1` after `self.peek()?`), REFUTED with `len(b) = 0, i = 0`,
//! because nothing in `bump` says `peek()` returned `Some` only if `i < len(b)` (design
//! §6 item 2, "`peek` composition", not built). `literal`'s untouched Return edge part
//! is next in line (an ay `self-check-rejected` unknown). No drop is `Situatedness`.
//! When item 2 lands, replace the `Refuted` NOTE with a `certified:` one.
//!
//! RE-MEASURED 2026-10-06 (TINV-18 second correction, the coarse call havoc;
//! CALL-HAVOC-ESCAPE-1): the dest-only call arm exempts only a `&mut` PARAMETER whose
//! pointee holds no pointer, and `P` holds `b: &[u8]`, so `Try::branch`/`len`/`eq` havoc
//! `*self` again. The first drop of `i <= len(b)` is now `bump`'s Return edge part from
//! `bb6` (the `?` path), REFUTED on the fresh post-call `self*` names; the `bb7` part is
//! still refuted behind it. Recovering `bb6` needs the exemption widened to shared
//! references to pointer-free `Freeze` data (reviewed separately), then item 2.
//!
//! RE-MEASURED 2026-10-06 (P1 precision: rule (b) widened to a pointee whose only
//! pointers are shared references to pointer-free `Freeze` data): `*self`'s own bytes survive
//! `Try::branch`/`len`/`eq` again, the `bb6` part is proved, and the first drop of
//! `i <= len(b)` is `bump`'s `bb7` part again (design item 2). Every other drop note is
//! unchanged in kind (`p1_realmir_tests` pins the rows).
//!
//! RE-MEASURED 2026-10-06 on the unit fixture of this crate's inventory (TINV-21, the
//! `peek` `Some`-arm lemma, merged with the rule-(b) widening and CALL-HAVOC-ESCAPE-2,
//! at the ay pin `630e4d62`): `i <= len(b)` CERTIFIES. Houdini drops `len(b) == i * i`,
//! `i <= 0` and `i <= 1` (Refuted) and certifies `i <= len(b)` alone over eight
//! kernel-certified rows; `bump`'s `bb7` row assumes `peek`'s two carried lemmas
//! (`p1_realmir_tests::p1_realmir_houdini_certifies_i_le_len_b`). The `on` annotations
//! below are written from that unit measurement. FIRST RUN under `x.py` (2026-10-07, stage 1
//! of the tinv/p1-precision landing merge): certified as measured; the `TINV:` and
//! `certified: 1 conjunct(s)` annotations named the SAME note (one diagnostic cannot
//! satisfy two annotations) and were merged into one.
#![forbid(unsafe_code)]

struct P<'a> {
    //[on]~^ NOTE TINV: type invariant of `tinv_p1_json_parser::P` certified: 1 conjunct(s), 8 kernel-certified row(s), 2 arm lemma(s) carried
    //[on]~^^ NOTE `i <= len(b)`
    //[on]~^^^ NOTE certified: #2 `i <= len(b)` (8 kernel-certified row(s), 2 arm lemma(s) carried
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

    fn literal(&mut self, w: &'static [u8]) -> bool {
        if self.b.len() >= self.i + w.len() && &self.b[self.i..self.i + w.len()] == w {
            self.i += w.len();
            true
        } else {
            false
        }
    }
}

pub fn parse(b: &[u8]) -> bool {
    let mut p = P { b, i: 0 };
    p.bump();
    p.literal(b"null")
}
