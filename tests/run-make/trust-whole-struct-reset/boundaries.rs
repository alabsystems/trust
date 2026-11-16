//! A missed complete type refuses only a reached store; dead stores stay dead.
#![allow(unreachable_code, unused_variables)]

pub struct Fat<'a> {
    pub value: &'a mut [u8],
    pub epoch: u64,
}

pub fn no_store<'a>(target: &mut Fat<'a>, value: Fat<'a>) {
    return;
    *target = value;
}

pub struct Generic<T> {
    pub value: T,
    pub epoch: u64,
}

pub fn generic_replacement<T>(target: &mut Generic<T>, value: Generic<T>) {
    let epoch = target.epoch;
    *target = value;
    target.epoch = epoch + 1;
}
