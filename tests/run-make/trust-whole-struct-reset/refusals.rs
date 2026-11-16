//! A complete replacement must not use an opaque or width-losing representation.

pub struct Fat<'a> {
    pub data: &'a mut [u8],
    pub epoch: u64,
}

pub fn fat_replacement<'a>(target: &mut Fat<'a>, value: Fat<'a>) {
    let epoch = target.epoch;
    *target = value;
    target.epoch = epoch + 1;
}

pub union Bits {
    pub wide: u64,
    pub narrow: u32,
}

pub struct WithUnion {
    pub bits: Bits,
    pub epoch: u64,
}

pub fn union_replacement(target: &mut WithUnion, value: WithUnion) {
    let epoch = target.epoch;
    *target = value;
    target.epoch = epoch + 1;
}
