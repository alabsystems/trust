#![allow(unused_assignments)]

// Every closure has one whole-variable scalar capture.

pub fn by_ref_capture() -> u32 {
    let mut value = 1u32;
    {
        let mut update = || {
            value += {
                value = 10;
                1
            };
        };
        update();
    }
    value
}

pub fn by_value_capture() -> u32 {
    let mut value = 1u32;
    let mut update = move || {
        value += {
            value = 10;
            1
        };
        value
    };
    update()
}

// With overflow checks enabled, Rust must return 1 without trapping.
pub fn rhs_removes_overflow() -> u8 {
    let mut value = u8::MAX;
    {
        let mut update = || {
            value += {
                value = 0;
                1
            };
        };
        update();
    }
    value
}

// With overflow checks enabled, Rust must trap at the compound assignment.
pub fn rhs_creates_overflow() -> u8 {
    let mut value = 0u8;
    {
        let mut update = || {
            value += {
                value = u8::MAX;
                1
            };
        };
        update();
    }
    value
}

pub fn unchanged_control() -> u32 {
    let mut value = 1u32;
    {
        let mut update = || value += 1;
        update();
    }
    value
}
