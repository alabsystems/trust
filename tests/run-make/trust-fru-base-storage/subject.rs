#![crate_type = "lib"]

pub struct Pair {
    pub first: u32,
    pub second: u32,
}

pub fn parameter_bound(mut value: u32) -> u32 {
    let base = {
        let reference = &mut value;
        *reference = 7;
        Pair { first: 0, second: *reference }
    };
    let pair = Pair { first: 1, ..base };
    pair.first ^ pair.second
}

pub fn parameter_hidden(mut value: u32) -> u32 {
    let pair = Pair {
        first: 1,
        ..{
            let reference = &mut value;
            *reference = 7;
            Pair { first: 0, second: *reference }
        }
    };
    pair.first ^ pair.second
}

pub fn local_bound(value: u32) -> u32 {
    let mut local = value;
    let base = {
        let reference = &mut local;
        *reference = 7;
        Pair { first: 0, second: *reference }
    };
    let pair = Pair { first: 1, ..base };
    pair.first ^ pair.second
}

pub fn local_hidden(value: u32) -> u32 {
    let mut local = value;
    let pair = Pair {
        first: 1,
        ..{
            let reference = &mut local;
            *reference = 7;
            Pair { first: 0, second: *reference }
        }
    };
    pair.first ^ pair.second
}

pub fn explicit_field_before_base(mut value: u32) -> u32 {
    let pair = Pair {
        first: {
            value = 3;
            1
        },
        ..{
            let reference = &mut value;
            let observed = *reference;
            *reference = 7;
            Pair { first: 0, second: observed }
        }
    };
    pair.first ^ pair.second
}
