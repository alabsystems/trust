pub fn f(s: &str) -> Vec<&str> { s.split(char::is_whitespace).collect() }
