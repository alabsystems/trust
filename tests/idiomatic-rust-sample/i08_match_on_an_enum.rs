pub enum Level { Debug, Info, Warn }
pub fn as_num(l: &Level) -> u8 { match l { Level::Debug => 0, Level::Info => 1, Level::Warn => 2 } }
