//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=strict --crate-type=lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Unwrap/expect panic-freedom from facts the body already established
//! (DECISION_QUEUE "UF-1", 2026-10-03). The obligation of a std
//! `Option`/`Result` `unwrap`/`expect` is "the receiver's discriminant is not the
//! panicking variant"; a dominating std probe, a `match`/`if let` on the same
//! subject, or a checked call result discharges it. On stage-1 aa965027e2 every
//! function in the first group failed the strict lane with
//! `Call::unwrap::panic-freedom-unverified`. The second group must keep failing:
//! nothing there establishes the variant at the call. The real-MIR twin of this
//! file is `crates/trust-vcgen/tests/unwrap_from_facts_realmir.rs`.

// The pointee of a shared `&` parameter, a field of it, an `as_ref` view of it,
// and a checked call result.
pub fn ref_is_some(x: &Option<u32>) -> u32 {
    if x.is_some() { x.unwrap() } else { 0 }
}
pub fn ref_match(x: &Option<u32>) -> u32 {
    match *x {
        Some(_) => x.unwrap(),
        None => 0,
    }
}
pub fn ref_if_let_expect(x: &Option<u32>) -> u32 {
    if let Some(_) = x { x.expect("checked") } else { 0 }
}
pub fn ref_as_ref(x: &Option<String>) -> usize {
    if x.is_some() { x.as_ref().unwrap().len() } else { 0 }
}
pub fn tuple_field(s: &(Option<u32>, u32)) -> u32 {
    if s.0.is_some() { s.0.unwrap() } else { 0 }
}
pub struct T {
    pub r: Result<u32, u8>,
}
pub fn struct_field_ok(t: &T) -> u32 {
    if t.r.is_ok() { t.r.unwrap() } else { 0 }
}
pub fn ok_or_result(x: Option<u32>) -> u32 {
    let r = x.ok_or(());
    if r.is_ok() { r.unwrap() } else { 0 }
}
pub fn ref_is_none_early(x: &Option<u32>) -> u32 {
    if x.is_none() {
        return 0;
    }
    x.unwrap()
}

// Controls.
pub fn ref_unchecked(x: &Option<u32>) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    x.unwrap()
}
pub fn ref_other(x: &Option<u32>, y: &Option<u32>) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    if x.is_some() { y.unwrap() } else { 0 }
}
pub fn ref_is_none_unwrap(x: &Option<u32>) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    if x.is_none() { x.unwrap() } else { 0 }
}
pub fn mut_between(x: &mut Option<u32>) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    if x.is_some() {
        *x = None;
        x.unwrap()
    } else {
        0
    }
}
pub fn mut_alias(x: &mut Option<u32>, f: fn(&mut Option<u32>)) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    if x.is_some() {
        f(x);
        x.unwrap()
    } else {
        0
    }
}
pub fn reseat<'a>(mut x: &'a Option<u32>, y: &'a Option<u32>) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    if x.is_some() {
        x = y;
        x.unwrap()
    } else {
        0
    }
}
pub fn ok_or_unchecked(x: Option<u32>) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    x.ok_or(()).unwrap()
}
pub struct W(pub Option<u32>);
impl W {
    // A user method named `unwrap`: its own std unwrap is unchecked...
    pub fn unwrap(&self) -> u32 {
        //~^ ERROR Trust Level 0 safety verification incomplete
        //~| ERROR Trust strict verification failed
        self.0.unwrap()
    }
}
// ...and its call site is not a std unwrap at all (resolved by item), so the
// caller owes nothing for it; the check on `w.0` is irrelevant either way.
pub fn user_unwrap(w: &W) -> u32 {
    if w.0.is_some() { w.unwrap() } else { 0 }
}
