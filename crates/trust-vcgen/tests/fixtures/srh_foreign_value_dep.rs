pub struct Cap {
    v: Vec<u8>,
}

impl Cap {
    pub fn new() -> Cap {
        Cap { v: Vec::new() }
    }
    pub fn len(&self) -> usize {
        self.v.len()
    }
}

pub fn val() -> u8 {
    7
}
