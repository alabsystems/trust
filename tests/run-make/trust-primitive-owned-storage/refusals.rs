#![allow(dead_code)]
// Borrowing the reference-valued leaf would require a reference-valued slot.
pub fn reference_slot<'a>(p: &'a mut i32, q: &'a mut i32) -> i32 {
    let (mut selected,) = (p,);
    let slot = &mut selected;
    *slot = q;
    **slot
}

// The primitive leaf repair does not authorize aggregate-valued homes.
pub fn aggregate_slot(a: i32, b: i32) -> i32 {
    let (mut selected,) = ((a, b),);
    let slot = &mut selected;
    slot.0 = b;
    slot.0
}

// Existing reference-parameter registration is deliberately unchanged.
pub fn char_parameter_store(dst: &mut char, value: char) { *dst = value; }
pub fn unit_parameter_store(dst: &mut (), value: ()) { *dst = value; }

// Reserving an actual Unit home does not authorize an indirect Unit store.
pub fn unit_indirect_store(flag: bool) {
    let mut local;
    if flag { local = (); } else { local = (); }
    let alias = &mut local;
    *alias = ();
}
