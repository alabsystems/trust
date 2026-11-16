pub struct FloatHolder { pub value: f32 }

pub fn shared_binding(value: f32) -> f32 {
    match value { ref borrowed => *borrowed }
}

pub fn guarded_binding(mut value: f32, replacement: f32, choose: bool) -> f32 {
    match value { ref mut borrowed if choose => *borrowed = replacement, _ => {} }
    value
}

pub fn subpattern_binding(mut value: f32, replacement: f32) -> f32 {
    match value { ref mut borrowed @ _ => *borrowed = replacement }
    value
}

pub fn value_temporary(value: f32, replacement: f32) -> f32 {
    match { value } { ref mut borrowed => *borrowed = replacement }
    value
}

pub fn field_place(mut holder: FloatHolder, replacement: f32) -> f32 {
    match holder.value { ref mut borrowed => *borrowed = replacement }
    holder.value
}

pub unsafe fn raw_pointer_place(target: *mut f32, replacement: f32) {
    unsafe { match *target { ref mut borrowed => *borrowed = replacement } }
}
