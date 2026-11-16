#![allow(unused_assignments, unused_labels)]

pub fn local_nested(n: u32) -> u32 {
    let mut total = 0u32;
    let mut i = 0u32;
    while i < 4 {
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            if total >= n % 7 + 1 { break; }
            j += 1;
        }
        i += 1;
    }
    total
}
pub fn outer_break(n: u32) -> u32 {
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 4 {
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            if total >= n % 7 + 1 { break 'outer; }
            j += 1;
        }
        i += 1;
    }
    total
}
pub fn outer_continue(n: u32) -> u32 {
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 4 {
        i += 1;
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            j += 1;
            if j == n % 3 + 1 { continue 'outer; }
        }
    }
    total
}
pub fn outer_break_value(n: u32) -> u32 {
    'outer: loop {
        let mut j = 0u32;
        loop {
            if j == n % 4 { break 'outer j + 9; }
            j += 1;
        }
    }
}

pub fn external_local_nested(n: u32) -> u32 {
    let mut total = 0u32;
    let mut i = 0u32;
    let mut j = 0u32;
    while i < 4 {
        j = 0;
        while j < 4 {
            total += 1;
            if total >= n % 7 + 1 { break; }
            j += 1;
        }
        i += 1;
    }
    total
}
pub fn external_outer_break(n: u32) -> u32 {
    let mut total = 0u32;
    let mut i = 0u32;
    let mut j = 0u32;
    'outer: while i < 4 {
        j = 0;
        while j < 4 {
            total += 1;
            if total >= n % 7 + 1 { break 'outer; }
            j += 1;
        }
        i += 1;
    }
    total
}
pub fn external_outer_continue(n: u32) -> u32 {
    let mut total = 0u32;
    let mut i = 0u32;
    let mut j = 0u32;
    'outer: while i < 4 {
        i += 1;
        j = 0;
        while j < 4 {
            total += 1;
            j += 1;
            if j == n % 3 + 1 { continue 'outer; }
        }
    }
    total
}
pub fn external_outer_break_value(n: u32) -> u32 {
    let mut j = 0u32;
    'outer: loop {
        j = 0;
        loop {
            if j == n % 4 { break 'outer j + 9; }
            j += 1;
        }
    }
}

pub fn three_levels(n: u32) -> u32 {
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 3 {
        i += 1;
        let mut j = 0u32;
        'middle: while j < 3 {
            j += 1;
            let mut k = 0u32;
            while k < 3 {
                k += 1;
                total += 1;
                if total >= n % 5 + 1 { break 'outer; }
                if k == 2 { continue 'middle; }
            }
        }
    }
    total
}
pub fn mixed_exits(n: u32) -> u32 {
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: loop {
        i += 1;
        let mut j = 0u32;
        loop {
            j += 1;
            total += 1;
            if j >= 2 { break; }
            if total >= n % 8 + 1 { break 'outer total + 10; }
        }
        if i >= 3 { break total + 20; }
    }
}
pub fn shadowed_labels() -> u32 {
    let mut total = 0u32;
    'target: loop {
        'target: loop {
            total += 3;
            break 'target;
        }
        total += 5;
        break 'target;
    }
    total
}
pub fn outer_block_is_not_a_loop() -> u32 {
    'outer: {
        'inner: {
            loop { break 'outer 17; }
        }
    }
}

pub fn local_nested_case_0() -> u32 {
    let n = 0u32;
    let mut total = 0u32;
    let mut i = 0u32;
    while i < 4 {
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            if total >= n % 7 + 1 { break; }
            j += 1;
        }
        i += 1;
    }
    total
}

pub fn local_nested_case_1() -> u32 {
    let n = 1u32;
    let mut total = 0u32;
    let mut i = 0u32;
    while i < 4 {
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            if total >= n % 7 + 1 { break; }
            j += 1;
        }
        i += 1;
    }
    total
}

pub fn local_nested_case_2() -> u32 {
    let n = 2u32;
    let mut total = 0u32;
    let mut i = 0u32;
    while i < 4 {
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            if total >= n % 7 + 1 { break; }
            j += 1;
        }
        i += 1;
    }
    total
}

pub fn local_nested_case_3() -> u32 {
    let n = 3u32;
    let mut total = 0u32;
    let mut i = 0u32;
    while i < 4 {
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            if total >= n % 7 + 1 { break; }
            j += 1;
        }
        i += 1;
    }
    total
}

pub fn local_nested_case_4() -> u32 {
    let n = 4u32;
    let mut total = 0u32;
    let mut i = 0u32;
    while i < 4 {
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            if total >= n % 7 + 1 { break; }
            j += 1;
        }
        i += 1;
    }
    total
}

pub fn local_nested_case_5() -> u32 {
    let n = 5u32;
    let mut total = 0u32;
    let mut i = 0u32;
    while i < 4 {
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            if total >= n % 7 + 1 { break; }
            j += 1;
        }
        i += 1;
    }
    total
}

pub fn local_nested_case_6() -> u32 {
    let n = 6u32;
    let mut total = 0u32;
    let mut i = 0u32;
    while i < 4 {
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            if total >= n % 7 + 1 { break; }
            j += 1;
        }
        i += 1;
    }
    total
}

pub fn local_nested_case_7() -> u32 {
    let n = 7u32;
    let mut total = 0u32;
    let mut i = 0u32;
    while i < 4 {
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            if total >= n % 7 + 1 { break; }
            j += 1;
        }
        i += 1;
    }
    total
}

pub fn outer_break_case_0() -> u32 {
    let n = 0u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 4 {
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            if total >= n % 7 + 1 { break 'outer; }
            j += 1;
        }
        i += 1;
    }
    total
}

pub fn outer_break_case_1() -> u32 {
    let n = 1u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 4 {
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            if total >= n % 7 + 1 { break 'outer; }
            j += 1;
        }
        i += 1;
    }
    total
}

pub fn outer_break_case_2() -> u32 {
    let n = 2u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 4 {
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            if total >= n % 7 + 1 { break 'outer; }
            j += 1;
        }
        i += 1;
    }
    total
}

pub fn outer_break_case_3() -> u32 {
    let n = 3u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 4 {
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            if total >= n % 7 + 1 { break 'outer; }
            j += 1;
        }
        i += 1;
    }
    total
}

pub fn outer_break_case_4() -> u32 {
    let n = 4u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 4 {
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            if total >= n % 7 + 1 { break 'outer; }
            j += 1;
        }
        i += 1;
    }
    total
}

pub fn outer_break_case_5() -> u32 {
    let n = 5u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 4 {
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            if total >= n % 7 + 1 { break 'outer; }
            j += 1;
        }
        i += 1;
    }
    total
}

pub fn outer_break_case_6() -> u32 {
    let n = 6u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 4 {
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            if total >= n % 7 + 1 { break 'outer; }
            j += 1;
        }
        i += 1;
    }
    total
}

pub fn outer_break_case_7() -> u32 {
    let n = 7u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 4 {
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            if total >= n % 7 + 1 { break 'outer; }
            j += 1;
        }
        i += 1;
    }
    total
}

pub fn outer_continue_case_0() -> u32 {
    let n = 0u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 4 {
        i += 1;
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            j += 1;
            if j == n % 3 + 1 { continue 'outer; }
        }
    }
    total
}

pub fn outer_continue_case_1() -> u32 {
    let n = 1u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 4 {
        i += 1;
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            j += 1;
            if j == n % 3 + 1 { continue 'outer; }
        }
    }
    total
}

pub fn outer_continue_case_2() -> u32 {
    let n = 2u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 4 {
        i += 1;
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            j += 1;
            if j == n % 3 + 1 { continue 'outer; }
        }
    }
    total
}

pub fn outer_continue_case_3() -> u32 {
    let n = 3u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 4 {
        i += 1;
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            j += 1;
            if j == n % 3 + 1 { continue 'outer; }
        }
    }
    total
}

pub fn outer_continue_case_4() -> u32 {
    let n = 4u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 4 {
        i += 1;
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            j += 1;
            if j == n % 3 + 1 { continue 'outer; }
        }
    }
    total
}

pub fn outer_continue_case_5() -> u32 {
    let n = 5u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 4 {
        i += 1;
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            j += 1;
            if j == n % 3 + 1 { continue 'outer; }
        }
    }
    total
}

pub fn outer_continue_case_6() -> u32 {
    let n = 6u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 4 {
        i += 1;
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            j += 1;
            if j == n % 3 + 1 { continue 'outer; }
        }
    }
    total
}

pub fn outer_continue_case_7() -> u32 {
    let n = 7u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 4 {
        i += 1;
        let mut j = 0u32;
        while j < 4 {
            total += 1;
            j += 1;
            if j == n % 3 + 1 { continue 'outer; }
        }
    }
    total
}

pub fn outer_break_value_case_0() -> u32 {
    let n = 0u32;
    'outer: loop {
        let mut j = 0u32;
        loop {
            if j == n % 4 { break 'outer j + 9; }
            j += 1;
        }
    }
}


pub fn outer_break_value_case_1() -> u32 {
    let n = 1u32;
    'outer: loop {
        let mut j = 0u32;
        loop {
            if j == n % 4 { break 'outer j + 9; }
            j += 1;
        }
    }
}


pub fn outer_break_value_case_2() -> u32 {
    let n = 2u32;
    'outer: loop {
        let mut j = 0u32;
        loop {
            if j == n % 4 { break 'outer j + 9; }
            j += 1;
        }
    }
}


pub fn outer_break_value_case_3() -> u32 {
    let n = 3u32;
    'outer: loop {
        let mut j = 0u32;
        loop {
            if j == n % 4 { break 'outer j + 9; }
            j += 1;
        }
    }
}


pub fn outer_break_value_case_4() -> u32 {
    let n = 4u32;
    'outer: loop {
        let mut j = 0u32;
        loop {
            if j == n % 4 { break 'outer j + 9; }
            j += 1;
        }
    }
}


pub fn outer_break_value_case_5() -> u32 {
    let n = 5u32;
    'outer: loop {
        let mut j = 0u32;
        loop {
            if j == n % 4 { break 'outer j + 9; }
            j += 1;
        }
    }
}


pub fn outer_break_value_case_6() -> u32 {
    let n = 6u32;
    'outer: loop {
        let mut j = 0u32;
        loop {
            if j == n % 4 { break 'outer j + 9; }
            j += 1;
        }
    }
}


pub fn outer_break_value_case_7() -> u32 {
    let n = 7u32;
    'outer: loop {
        let mut j = 0u32;
        loop {
            if j == n % 4 { break 'outer j + 9; }
            j += 1;
        }
    }
}


pub fn three_levels_case_0() -> u32 {
    let n = 0u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 3 {
        i += 1;
        let mut j = 0u32;
        'middle: while j < 3 {
            j += 1;
            let mut k = 0u32;
            while k < 3 {
                k += 1;
                total += 1;
                if total >= n % 5 + 1 { break 'outer; }
                if k == 2 { continue 'middle; }
            }
        }
    }
    total
}

pub fn three_levels_case_1() -> u32 {
    let n = 1u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 3 {
        i += 1;
        let mut j = 0u32;
        'middle: while j < 3 {
            j += 1;
            let mut k = 0u32;
            while k < 3 {
                k += 1;
                total += 1;
                if total >= n % 5 + 1 { break 'outer; }
                if k == 2 { continue 'middle; }
            }
        }
    }
    total
}

pub fn three_levels_case_2() -> u32 {
    let n = 2u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 3 {
        i += 1;
        let mut j = 0u32;
        'middle: while j < 3 {
            j += 1;
            let mut k = 0u32;
            while k < 3 {
                k += 1;
                total += 1;
                if total >= n % 5 + 1 { break 'outer; }
                if k == 2 { continue 'middle; }
            }
        }
    }
    total
}

pub fn three_levels_case_3() -> u32 {
    let n = 3u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 3 {
        i += 1;
        let mut j = 0u32;
        'middle: while j < 3 {
            j += 1;
            let mut k = 0u32;
            while k < 3 {
                k += 1;
                total += 1;
                if total >= n % 5 + 1 { break 'outer; }
                if k == 2 { continue 'middle; }
            }
        }
    }
    total
}

pub fn three_levels_case_4() -> u32 {
    let n = 4u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 3 {
        i += 1;
        let mut j = 0u32;
        'middle: while j < 3 {
            j += 1;
            let mut k = 0u32;
            while k < 3 {
                k += 1;
                total += 1;
                if total >= n % 5 + 1 { break 'outer; }
                if k == 2 { continue 'middle; }
            }
        }
    }
    total
}

pub fn three_levels_case_5() -> u32 {
    let n = 5u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 3 {
        i += 1;
        let mut j = 0u32;
        'middle: while j < 3 {
            j += 1;
            let mut k = 0u32;
            while k < 3 {
                k += 1;
                total += 1;
                if total >= n % 5 + 1 { break 'outer; }
                if k == 2 { continue 'middle; }
            }
        }
    }
    total
}

pub fn three_levels_case_6() -> u32 {
    let n = 6u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 3 {
        i += 1;
        let mut j = 0u32;
        'middle: while j < 3 {
            j += 1;
            let mut k = 0u32;
            while k < 3 {
                k += 1;
                total += 1;
                if total >= n % 5 + 1 { break 'outer; }
                if k == 2 { continue 'middle; }
            }
        }
    }
    total
}

pub fn three_levels_case_7() -> u32 {
    let n = 7u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: while i < 3 {
        i += 1;
        let mut j = 0u32;
        'middle: while j < 3 {
            j += 1;
            let mut k = 0u32;
            while k < 3 {
                k += 1;
                total += 1;
                if total >= n % 5 + 1 { break 'outer; }
                if k == 2 { continue 'middle; }
            }
        }
    }
    total
}

pub fn mixed_exits_case_0() -> u32 {
    let n = 0u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: loop {
        i += 1;
        let mut j = 0u32;
        loop {
            j += 1;
            total += 1;
            if j >= 2 { break; }
            if total >= n % 8 + 1 { break 'outer total + 10; }
        }
        if i >= 3 { break total + 20; }
    }
}

pub fn mixed_exits_case_1() -> u32 {
    let n = 1u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: loop {
        i += 1;
        let mut j = 0u32;
        loop {
            j += 1;
            total += 1;
            if j >= 2 { break; }
            if total >= n % 8 + 1 { break 'outer total + 10; }
        }
        if i >= 3 { break total + 20; }
    }
}

pub fn mixed_exits_case_2() -> u32 {
    let n = 2u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: loop {
        i += 1;
        let mut j = 0u32;
        loop {
            j += 1;
            total += 1;
            if j >= 2 { break; }
            if total >= n % 8 + 1 { break 'outer total + 10; }
        }
        if i >= 3 { break total + 20; }
    }
}

pub fn mixed_exits_case_3() -> u32 {
    let n = 3u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: loop {
        i += 1;
        let mut j = 0u32;
        loop {
            j += 1;
            total += 1;
            if j >= 2 { break; }
            if total >= n % 8 + 1 { break 'outer total + 10; }
        }
        if i >= 3 { break total + 20; }
    }
}

pub fn mixed_exits_case_4() -> u32 {
    let n = 4u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: loop {
        i += 1;
        let mut j = 0u32;
        loop {
            j += 1;
            total += 1;
            if j >= 2 { break; }
            if total >= n % 8 + 1 { break 'outer total + 10; }
        }
        if i >= 3 { break total + 20; }
    }
}

pub fn mixed_exits_case_5() -> u32 {
    let n = 5u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: loop {
        i += 1;
        let mut j = 0u32;
        loop {
            j += 1;
            total += 1;
            if j >= 2 { break; }
            if total >= n % 8 + 1 { break 'outer total + 10; }
        }
        if i >= 3 { break total + 20; }
    }
}

pub fn mixed_exits_case_6() -> u32 {
    let n = 6u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: loop {
        i += 1;
        let mut j = 0u32;
        loop {
            j += 1;
            total += 1;
            if j >= 2 { break; }
            if total >= n % 8 + 1 { break 'outer total + 10; }
        }
        if i >= 3 { break total + 20; }
    }
}

pub fn mixed_exits_case_7() -> u32 {
    let n = 7u32;
    let mut total = 0u32;
    let mut i = 0u32;
    'outer: loop {
        i += 1;
        let mut j = 0u32;
        loop {
            j += 1;
            total += 1;
            if j >= 2 { break; }
            if total >= n % 8 + 1 { break 'outer total + 10; }
        }
        if i >= 3 { break total + 20; }
    }
}

pub fn bare_outer_break() -> u32 {
    'outer: loop {
        loop { break 'outer; }
    }
    29
}

pub fn outer_break_in_else(value: Option<u32>) -> u32 {
    'outer: loop {
        loop {
            let Some(n) = value else { break 'outer; };
            return n;
        }
    }
    29
}

pub fn outer_continue_in_else(value: Option<u32>) -> u32 {
    let mut first = true;
    'outer: loop {
        if !first { return 29; }
        first = false;
        loop {
            let Some(n) = value else { continue 'outer; };
            return n;
        }
    }
}
