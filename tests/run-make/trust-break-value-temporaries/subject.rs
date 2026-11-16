#![crate_type = "lib"]

pub fn parameter_before_break(mut value: u32) -> u32 {
    loop {
        let reference = &mut value;
        *reference = 7;
        break *reference;
    }
}

pub fn parameter_in_break(mut value: u32) -> u32 {
    loop {
        break {
            let reference = &mut value;
            *reference = 7;
            *reference
        };
    }
}

pub fn local_before_break(value: u32) -> u32 {
    let mut local = value;
    loop {
        let reference = &mut local;
        *reference = 7;
        break *reference;
    }
}

pub fn local_in_break(value: u32) -> u32 {
    let mut local = value;
    loop {
        break {
            let reference = &mut local;
            *reference = 7;
            *reference
        };
    }
}
