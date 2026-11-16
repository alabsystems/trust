#![allow(unused_assignments, unused_variables, unreachable_patterns, unconditional_panic)]

pub fn literal_true() -> u32 {
    let mut n = 1;
    let v = match 0 {
        0 if {
            n += 2;
            true
        } =>
        {
            n + 10
        }
        _ => 99,
    };
    n + v
}
pub fn literal_false() -> u32 {
    let mut n = 1;
    let v = match 0 {
        0 if {
            n += 2;
            false
        } =>
        {
            99
        }
        _ => n * 10,
    };
    n + v
}
pub fn catch_all(value: u32) -> u32 {
    let mut n = 1;
    let v = match value {
        x if {
            n += x & 7;
            true
        } =>
        {
            n
        }
        _ => 99,
    };
    n + v
}
pub fn chained_guards() -> u32 {
    let mut n = 0;
    let v = match 0 {
        _ if {
            n += 1;
            false
        } =>
        {
            99
        }
        _ if {
            n += 2;
            true
        } =>
        {
            n
        }
        _ => 77,
    };
    n * 10 + v
}
pub fn case_then_catch(value: u32) -> u32 {
    let mut n = 1;
    let v = match value {
        0 if {
            n += 2;
            false
        } =>
        {
            99
        }
        x if {
            n += 3;
            true
        } =>
        {
            n + (x & 7)
        }
        _ => 77,
    };
    n * 10 + v
}
pub fn guard_then_range(value: u32) -> u32 {
    let mut n = 0;
    let v = match value {
        _ if {
            n += 1;
            false
        } =>
        {
            99
        }
        0..=3 => n + 10,
        _ => n + 20,
    };
    n + v
}
pub fn looped() -> u32 {
    let mut n = 0;
    let mut state = 0;
    loop {
        state = match state {
            0 if {
                n += 1;
                true
            } =>
            {
                1
            }
            1 if {
                n += 1;
                true
            } =>
            {
                2
            }
            _ => break,
        };
    }
    n
}
pub fn guard_local_shadow() -> u32 {
    let n = 7;
    let v = match 0 {
        0 if {
            let mut n = 10;
            n += 1;
            n == 11
        } =>
        {
            n
        }
        _ => 99,
    };
    n + v
}
pub fn mutable_parameter(mut n: u32) -> u32 {
    let _ = match 0 {
        0 if {
            n = n & 7;
            true
        } =>
        {
            n
        }
        _ => 99,
    };
    n
}
pub fn checked_guard(flag: bool) -> u32 {
    let mut n = 1;
    let v = match 0 {
        0 if {
            assert!(flag);
            n += 2;
            true
        } =>
        {
            n
        }
        _ => 99,
    };
    n + v
}
pub fn array_guard() -> u32 {
    let mut words = [1u32, 2];
    let v = match 0 {
        0 if {
            words[0] += 3;
            false
        } =>
        {
            99
        }
        _ => words[0] + words[1],
    };
    v + words[0]
}
pub fn successive_matches() -> u32 {
    let mut n = 1;
    let _ = match 0 {
        0 if {
            n += 2;
            false
        } =>
        {
            99
        }
        _ => n,
    };
    let v = match 1 {
        1 if {
            n *= 2;
            true
        } =>
        {
            n
        }
        _ => 99,
    };
    n + v
}
pub fn nested_guard() -> u32 {
    let mut n = 0;
    let v = match 0 {
        0 if {
            let t = match 0 {
                0 if {
                    n += 2;
                    false
                } =>
                {
                    99
                }
                _ => n,
            };
            t == 2
        } =>
        {
            n
        }
        _ => 99,
    };
    n + v
}
pub fn asm_refused() -> u32 {
    let mut n = 0;
    let v = match 0 {
        0 if {
            unsafe {
                core::arch::asm!("");
            }
            n += 1;
            true
        } =>
        {
            n
        }
        _ => 99,
    };
    n + v
}

pub fn array_guard_rhs() -> u32 {
    let mut words = [1u32, 2];
    match 0 {
        0 if {
            words[0] += {
                words = [7, 8];
                3
            };
            false
        } =>
        {
            99
        }
        _ => words[0] + words[1],
    }
}

pub fn array_guard_overflow() -> u32 {
    let mut words = [u32::MAX, 2];
    match 0 {
        0 if {
            words[0] += 1;
            true
        } =>
        {
            words[0]
        }
        _ => 0,
    }
}

pub fn array_guard_oob_refused() -> u32 {
    let mut words = [1u32, 2];
    match 0 {
        0 if {
            words[9] += 1;
            true
        } =>
        {
            99
        }
        _ => 7,
    }
}

pub fn unit_guard() -> u32 {
    let mut unit = ();
    match 0 {
        0 if {
            unit = ();
            true
        } =>
        {
            7
        }
        _ => 9,
    }
}

pub fn unit_guard_rhs_assignment() -> u32 {
    let mut unit = ();
    let mut count = 0;
    match 0 {
        0 if {
            unit = count = 7;
            false
        } =>
        {
            99
        }
        _ => count,
    }
}

pub fn unit_guard_rhs_overflow() -> u32 {
    let mut unit = ();
    let mut count = u32::MAX;
    match 0 {
        0 if {
            unit = count += 1;
            true
        } =>
        {
            7
        }
        _ => 9,
    }
}

pub fn unrelated_guard_shadow() -> u32 {
    let n = 7;
    match 0 {
        0 if {
            let mut n = 2;
            n += 1;
            n == 3
        } =>
        {
            n
        }
        _ => 9,
    }
}

pub fn ssa_cast_base() -> u32 {
    let mut a = [1u32, 2];
    (a as [u32; 2])[0] += 3;
    a[0]
}

pub fn promoted_cast_base() -> u32 {
    let mut a = [1u32, 2];
    let _pin = &mut a;
    (a as [u32; 2])[0] += 3;
    a[0]
}

pub fn guard_cast_base() -> u32 {
    let mut a = [1u32, 2];
    match 0 {
        0 if {
            (a as [u32; 2])[0] += 3;
            false
        } =>
        {
            99
        }
        _ => a[0],
    }
}

pub fn cast_rhs_replaces_base() -> u32 {
    let mut a = [u32::MAX, 2];
    (a as [u32; 2])[0] += {
        a = [7, 8];
        3
    };
    a[0]
}
