#![crate_type = "lib"]

pub fn borrowed_result(mut value: u32) -> u32 {
    let reference = loop {
        break &mut value;
    };
    *reference
}

pub fn outer_label(mut value: u32) -> u32 {
    'outer: loop {
        loop {
            break 'outer {
                let reference = &mut value;
                *reference = 7;
                *reference
            };
        }
    }
}
