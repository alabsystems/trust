pub fn first_field(line: &str) -> &str { line.split(',').next().unwrap_or("") }
