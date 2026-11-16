#![crate_type = "lib"]
#![feature(type_ascription)]

pub fn direct() -> u32 {
    let mut tick = 0u32;
    let mut sum = 0u32;
    loop {
        tick += 1;
        let _ = { sum += 1; sum };
        if tick >= 3 { break sum; }
    }
}

pub fn cast() -> u32 {
    let mut tick = 0u32;
    let mut sum = 0u32;
    loop {
        tick += 1;
        let _ = ({ sum += 1; sum } as u64);
        if tick >= 3 { break sum; }
    }
}

pub fn value_ascribed() -> u32 {
    let mut tick = 0u32;
    let mut sum = 0u32;
    loop {
        tick += 1;
        let _ = type_ascribe!({ sum += 1; sum }, u32);
        if tick >= 3 { break sum; }
    }
}

pub fn index_direct() -> u32 {
    let array = [9u32];
    let mut tick = 0u32;
    let mut sum = 0u32;
    loop {
        tick += 1;
        let _ = array[{ sum += 1; 0usize }];
        if tick >= 3 { break sum; }
    }
}

pub fn place_ascribed() -> u32 {
    let array = [9u32];
    let mut tick = 0u32;
    let mut sum = 0u32;
    loop {
        tick += 1;
        let _ = type_ascribe!(array[{ sum += 1; 0usize }], u32);
        if tick >= 3 { break sum; }
    }
}

pub fn nested_direct() -> u32 {
    let mut tick = 0u32;
    let mut sum = 0u32;
    loop {
        tick += 1;
        let _ = {
            loop { sum += 1; break; }
            0u32
        };
        if tick >= 3 { break sum; }
    }
}

pub fn nested_cast() -> u32 {
    let mut tick = 0u32;
    let mut sum = 0u32;
    loop {
        tick += 1;
        let _ = ({
            loop { sum += 1; break; }
            0u32
        } as u64);
        if tick >= 3 { break sum; }
    }
}
