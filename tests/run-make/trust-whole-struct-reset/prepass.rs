//! Rejected dead replacements must not mutate live type-lowering state.
#![feature(f16)]
#![allow(dead_code, unreachable_code, unused_variables)]

pub struct Half {
    pub value: f16,
}

pub union Bits {
    pub value: u64,
}

pub struct WithUnion {
    pub bits: Bits,
    pub epoch: u64,
}

#[repr(C)]
pub struct Cell {
    pub guard: u32,
    pub field: u32,
}

pub unsafe fn dead_half_write(target: *mut Half) -> u32 {
    return 7;
    unsafe { *target = loop {}; }
}

pub unsafe fn dead_union_write(target: *mut WithUnion) -> u32 {
    return 9;
    unsafe { *target = loop {}; }
}

pub unsafe fn rejected_before_valid(target: *mut WithUnion) -> u32 {
    'skip: {
        break 'skip;
        unsafe { *target = loop {}; }
    }
    let mut cell = Cell { guard: 1, field: 2 };
    let reference = &mut cell;
    let prior = reference.guard;
    *reference = Cell { guard: 3, field: 4 };
    reference.guard = prior + 5;
    cell.guard * 100 + cell.field
}

pub unsafe fn valid_before_rejected(target: *mut WithUnion) -> u32 {
    let mut cell = Cell { guard: 1, field: 2 };
    let reference = &mut cell;
    let prior = reference.guard;
    *reference = Cell { guard: 3, field: 4 };
    reference.guard = prior + 5;
    return cell.guard * 100 + cell.field;
    unsafe { *target = loop {}; }
}

// A rejection from actually mapping a source parameter must survive the probe.
pub fn reached_half(target: &mut Half, value: Half) {
    *target = value;
}

pub fn reached_union(target: &mut WithUnion, value: WithUnion) {
    *target = value;
}

pub struct Fat<'a> {
    pub value: &'a mut [u8],
    pub epoch: u64,
}

pub fn reached_fat<'a>(target: &mut Fat<'a>, value: Fat<'a>) {
    *target = value;
}

pub fn prepass_runtime() -> u32 {
    unsafe {
        dead_half_write(0usize as *mut Half)
            + dead_union_write(0usize as *mut WithUnion)
            + rejected_before_valid(0usize as *mut WithUnion)
            + valid_before_rejected(0usize as *mut WithUnion)
    }
}
