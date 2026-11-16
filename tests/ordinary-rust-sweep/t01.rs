pub struct Cfg {
    pub retries: u8,
    pub name: String,
}
impl Cfg {
    pub fn with_retries(mut self, r: u8) -> Cfg {
        self.retries = r;
        self
    }
}
