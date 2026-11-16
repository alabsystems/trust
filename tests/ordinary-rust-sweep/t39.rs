pub fn map_err_to_unit(r: Result<u32, String>) -> Result<u32, ()> {
    r.map_err(|_| ())
}
