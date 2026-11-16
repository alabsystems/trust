#![allow(unused_assignments, unused_mut, break_with_label_and_loop)]

pub fn inner(flag: bool) -> u32 {
    let mut x = 1u32;
    let y = loop {
        if flag { break { x = 7; 11u32 }; }
        break 13u32;
    };
    x + y
}
pub fn both_arms(flag: bool) -> u32 {
    let mut x = 1u32;
    let y = loop {
        if flag { break { x = 7; 11u32 }; }
        break { x = 9; 13u32 };
    };
    x + y
}
pub fn outer(flag: bool) -> u32 {
    let mut x = 1u32;
    let y = 'out: loop {
        loop {
            if flag { break 'out { x = 7; 11u32 }; }
            break 'out 13u32;
        }
    };
    x + y
}

pub fn local_temp() -> u32 {
    loop { break { let mut x = 1u32; x = 7; x + 11 }; }
}
pub fn local_before_value() -> u32 {
    loop { let mut t = 1u32; break { t = 7; t + 11 }; }
}
pub fn direct_outer_assignment() -> u32 {
    let mut x = 1u32;
    let y = loop { break { x = 7; 11u32 }; };
    x + y
}
pub fn mixed_locals() -> u32 {
    let mut x = 1u32;
    let y = loop { break { let mut t = 1u32; t = 7; x = 9; t + 11 }; };
    x + y
}
pub fn shadowed_local() -> u32 {
    let x = 1u32;
    let y = loop { break { let mut x = 3u32; x = 7; x + 11 }; };
    x + y
}
pub fn destructured_locals() -> u32 {
    loop { break { let (mut a, mut b) = (1u32, 2u32); a = 7; b = 9; a + b }; }
}
pub fn uninitialized_external() -> u32 {
    let mut x: u32;
    let y = loop { break { x = 7; 11u32 }; };
    x + y
}

pub fn inner_false() -> u32 {
    let flag = false;
    let mut x = 1u32;
    let y = loop {
        if flag { break { x = 7; 11u32 }; }
        break 13u32;
    };
    x + y
}

pub fn inner_true() -> u32 {
    let flag = true;
    let mut x = 1u32;
    let y = loop {
        if flag { break { x = 7; 11u32 }; }
        break 13u32;
    };
    x + y
}

pub fn both_arms_false() -> u32 {
    let flag = false;
    let mut x = 1u32;
    let y = loop {
        if flag { break { x = 7; 11u32 }; }
        break { x = 9; 13u32 };
    };
    x + y
}

pub fn both_arms_true() -> u32 {
    let flag = true;
    let mut x = 1u32;
    let y = loop {
        if flag { break { x = 7; 11u32 }; }
        break { x = 9; 13u32 };
    };
    x + y
}

pub fn outer_false() -> u32 {
    let flag = false;
    let mut x = 1u32;
    let y = 'out: loop {
        loop {
            if flag { break 'out { x = 7; 11u32 }; }
            break 'out 13u32;
        }
    };
    x + y
}


pub fn outer_true() -> u32 {
    let flag = true;
    let mut x = 1u32;
    let y = 'out: loop {
        loop {
            if flag { break 'out { x = 7; 11u32 }; }
            break 'out 13u32;
        }
    };
    x + y
}


pub fn mixed_shadowed(flag: bool) -> u32 {
    let mut x = 1u32;
    let y = loop {
        if flag {
            break {
                x = 7;
                let mut x = 3u32;
                x = 9;
                x + 11
            };
        }
        break 13u32;
    };
    x + y
}

pub fn nested_value(flag: bool) -> u32 {
    let mut x = 1u32;
    let y = loop {
        break {
            let z = loop {
                if flag { break { x = 7; 11u32 }; }
                break 13u32;
            };
            z + 2
        };
    };
    x + y
}
pub fn mixed_shadowed_false() -> u32 {
    let flag = false;
    let mut x = 1u32;
    let y = loop {
        if flag {
            break {
                x = 7;
                let mut x = 3u32;
                x = 9;
                x + 11
            };
        }
        break 13u32;
    };
    x + y
}
pub fn mixed_shadowed_true() -> u32 {
    let flag = true;
    let mut x = 1u32;
    let y = loop {
        if flag {
            break {
                x = 7;
                let mut x = 3u32;
                x = 9;
                x + 11
            };
        }
        break 13u32;
    };
    x + y
}
pub fn nested_value_false() -> u32 {
    let flag = false;
    let mut x = 1u32;
    let y = loop {
        break {
            let z = loop {
                if flag { break { x = 7; 11u32 }; }
                break 13u32;
            };
            z + 2
        };
    };
    x + y
}pub fn nested_value_true() -> u32 {
    let flag = true;
    let mut x = 1u32;
    let y = loop {
        break {
            let z = loop {
                if flag { break { x = 7; 11u32 }; }
                break 13u32;
            };
            z + 2
        };
    };
    x + y
}