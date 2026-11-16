#[derive(Clone)]
pub struct Cfg { pub host: u32, pub port: u16, pub retries: u8 }
pub fn with_port(c: &Cfg, port: u16) -> Cfg { Cfg { port, ..c.clone() } }
