#[inline(never)]
pub fn store_f32(target: &mut f32, value: f32) { *target = value; }
#[inline(never)]
pub fn store_f64(target: &mut f64, value: f64) { *target = value; }
#[inline(never)]
pub fn read_f32(target: &f32) -> f32 { *target }
#[inline(never)]
pub fn read_f64(target: &f64) -> f64 { *target }

#[inline(never)]
pub fn replace_f32(initial: f32, replacement: f32) -> f32 {
    let mut local = initial;
    store_f32(&mut local, replacement);
    read_f32(&local)
}
#[inline(never)]
pub fn replace_f64(initial: f64, replacement: f64) -> f64 {
    let mut local = initial;
    store_f64(&mut local, replacement);
    read_f64(&local)
}

#[inline(never)]
pub fn branch_f32(initial: f32, left: f32, right: f32, choose: bool) -> f32 {
    let mut local = initial;
    if choose { store_f32(&mut local, left); } else { store_f32(&mut local, right); }
    read_f32(&local)
}
#[inline(never)]
pub fn branch_f64(initial: f64, left: f64, right: f64, choose: bool) -> f64 {
    let mut local = initial;
    if choose { store_f64(&mut local, left); } else { store_f64(&mut local, right); }
    read_f64(&local)
}

#[inline(never)]
pub fn pattern_f32(initial: f32, replacement: f32) -> f32 {
    let mut local = initial;
    match local { ref mut borrowed => *borrowed = replacement }
    read_f32(&local)
}
#[inline(never)]
pub fn pattern_f64(initial: f64, replacement: f64) -> f64 {
    let mut local = initial;
    match local { ref mut borrowed => *borrowed = replacement }
    read_f64(&local)
}

#[inline(never)]
pub fn raw_local_f32(initial: f32, replacement: f32) -> f32 {
    let mut local = initial;
    let pointer = &raw mut local;
    unsafe { *pointer = replacement; }
    read_f32(&local)
}
#[inline(never)]
pub fn raw_local_f64(initial: f64, replacement: f64) -> f64 {
    let mut local = initial;
    let pointer = &raw mut local;
    unsafe { *pointer = replacement; }
    read_f64(&local)
}

#[inline(never)]
pub fn delayed_f32(first: f32, second: f32, choose: bool) -> f32 {
    let mut local;
    if choose { local = first; } else { local = second; }
    let value = read_f32(&local);
    store_f32(&mut local, value);
    read_f32(&local)
}
#[inline(never)]
pub fn delayed_f64(first: f64, second: f64, choose: bool) -> f64 {
    let mut local;
    if choose { local = first; } else { local = second; }
    let value = read_f64(&local);
    store_f64(&mut local, value);
    read_f64(&local)
}

#[inline(never)]
pub fn parameter_f32(mut value: f32, replacement: f32) -> f32 {
    store_f32(&mut value, replacement);
    read_f32(&value)
}
#[inline(never)]
pub fn parameter_f64(mut value: f64, replacement: f64) -> f64 {
    store_f64(&mut value, replacement);
    read_f64(&value)
}
