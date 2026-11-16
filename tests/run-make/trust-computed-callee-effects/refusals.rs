#![crate_type = "lib"]

pub fn identity(value: u32) -> u32 { value }

pub fn conditional(choose: bool, mut count: u32) -> u32 {
    (if choose { count += 1; identity } else { count += 2; identity })(count)
}

pub fn matched(choose: u32, mut count: u32) -> u32 {
    (match choose {
        0 => { count += 1; identity }
        _ => { count += 2; identity }
    })(count)
}

pub fn labeled(mut count: u32) -> u32 {
    ('callee: { count += 1; break 'callee identity; })(count)
}
