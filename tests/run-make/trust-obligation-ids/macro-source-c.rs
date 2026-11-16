// Trust: change the template and one ordinary function, leaving invocations fixed.
macro_rules! define_div {
    ($name:ident, $offset:expr) => {
        pub fn $name(n: u64, d: u64) -> u64 {
            (n / (d + $offset)).wrapping_add(0)
        }
    };
}

define_div!(generated, 4);
define_div!(neighbor, 3);

pub fn ordinary(n: u64, d: u64) -> u64 {
    n / (d + 5)
}

pub fn untouched(n: u64) -> u64 {
    n + 1
}
