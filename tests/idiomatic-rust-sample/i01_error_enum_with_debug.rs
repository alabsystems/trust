#[derive(Debug)]
pub enum ConfigError { Missing(&'static str), Invalid { key: &'static str, got: u32 } }
pub fn check(port: u32) -> Result<u32, ConfigError> {
    if port == 0 { return Err(ConfigError::Missing("port")); }
    if port > 65535 { return Err(ConfigError::Invalid { key: "port", got: port }); }
    Ok(port)
}
