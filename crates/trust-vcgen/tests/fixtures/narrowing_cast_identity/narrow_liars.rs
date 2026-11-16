// VC-NARROW-CAST-FALSE-REFUTE-1 real-MIR fixture: every function here panics for
// some input; none may be proved.
pub fn l1(x: u32) -> u8 { let arr = [0u8; 0x80]; if x <= 0x80 { arr[x as u8 as usize] } else { 0 } }
pub fn l2(x: u32) -> u8 { let arr = [0u8; 0x7f]; if x < 0x80 { arr[x as u8 as usize] } else { 0 } }
pub fn l3(x: u32) -> u8 { let arr = [0u8; 0x80]; if x < 0x180 { arr[x as u8 as usize] } else { 0 } }
// The guard reads `y` AFTER it is rewritten: the cast saw the old value.
pub fn st1(x: u32) -> u8 {
    let arr = [0u8; 0x80];
    let mut y = x;
    let b = y as u8;
    y = 0;
    if y < 0x80 { arr[b as usize] } else { 0 }
}
// Loop-carried: `b` is the previous element's cast, the guard tests the current one.
pub fn st2(xs: &[u32]) -> u8 {
    let arr = [0u8; 0x80];
    let mut b = 0u8;
    let mut r = 0u8;
    for &y in xs {
        if y < 0x80 { r = arr[b as usize]; }
        b = y as u8;
    }
    r
}
// Loop-carried through a counter: `b` is cast from `y` before `y` is rebound.
pub fn st3(x: u32, n: u32) -> u8 {
    let arr = [0u8; 0x80];
    let mut y = x;
    let mut r = 0u8;
    let mut i = 0u32;
    while i < n {
        let b = y as u8;
        y = i;
        if y < 0x80 { r = arr[b as usize]; }
        i += 1;
    }
    r
}
pub fn add_l(x: u32) -> u8 { if x <= 0x81 { (x as u8) + 0x7f } else { 0 } }
pub fn shl_l(x: u32) -> u32 { if x <= 0x20 { 1u32 << (x as u8) } else { 0 } }
