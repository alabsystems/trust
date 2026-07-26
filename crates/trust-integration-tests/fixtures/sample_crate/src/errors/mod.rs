// Error handling patterns: Result, Option chaining.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub fn option_to_result(opt: Option<i32>) -> Result<i32, &'static str> {
    opt.ok_or("none")
}

pub fn result_to_option(res: Result<i32, ()>) -> Option<i32> {
    res.ok()
}

pub fn unwrap_or_zero(opt: Option<i32>) -> i32 {
    opt.unwrap_or(0)
}

pub fn map_result(res: Result<i32, ()>) -> Result<i32, ()> {
    res.map(|x| x + 1)
}

pub fn and_then_result(res: Result<i32, ()>) -> Result<i32, ()> {
    res.and_then(|x| if x > 0 { Ok(x) } else { Err(()) })
}

pub fn or_else_result(res: Result<i32, ()>) -> Result<i32, ()> {
    res.or_else(|_| Ok(0))
}
