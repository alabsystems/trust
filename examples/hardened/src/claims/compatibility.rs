use std::env;

pub(crate) fn compatibility_observable_boundary() -> Vec<String> {
    let mut direct: Vec<String> = std::env::args().collect();
    direct.extend(env::args());
    direct
}
