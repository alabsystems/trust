use core::fmt;
pub struct Port(pub u16);
impl fmt::Display for Port { fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { f.write_str("port") } }
