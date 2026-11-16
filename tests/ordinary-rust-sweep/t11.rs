pub fn opt_default(o: Option<&str>) -> &str {
    o.unwrap_or("none")
}
