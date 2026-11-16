#![allow(unused_assignments, unused_variables, unreachable_code, unconditional_panic)]

const UNIT: () = ();

pub fn once() -> u32 {
    let mut n = 0;
    let _ = [{
        n += 1;
    }; 4];
    n
}

pub fn zero() -> u32 {
    let mut n = 0;
    let _ = [{
        n += 1;
    }; 0];
    n
}

pub fn looped() -> u32 {
    let mut n = 0;
    let mut iterations = 0;
    loop {
        iterations += 1;
        let _ = [{
            n += 1;
        }; 4];
        if iterations == 3 {
            break n;
        }
    }
}

pub fn branches(flag: bool) -> u32 {
    let mut n = 0;
    let _ = [{
        if flag {
            n += 2;
        } else {
            n += 5;
        }
    }; 8];
    n
}

pub fn nested() -> u32 {
    let mut n = 0;
    let _ = [{
        let _ = [{
            n += 1;
        }; 2];
        n += 2;
    }; 3];
    n
}

pub fn many() -> u32 {
    let mut n = 0;
    let _ = [{
        n += 1;
    }; 1_048_576];
    n
}

pub fn early_return() -> u32 {
    let _: [(); 5] = [{
        return 7;
    }; 5];
    99
}

pub fn from_named() -> u32 {
    let mut n = 0;
    let _ = [{
        n += 1;
        UNIT
    }; 2];
    n
}

pub fn indexed() -> u32 {
    let mut n = 0;
    let units = [{
        n += 1;
    }; 4];
    let _ = units[3];
    n
}

pub fn checked(flag: bool) -> u32 {
    let mut n = 0;
    let _ = [{
        assert!(flag);
        n += 1;
    }; 8];
    n
}

pub fn asm_refused() -> u32 {
    let _ = [{
        unsafe {
            core::arch::asm!("");
        }
    }; 4];
    7
}

pub fn asm_then_return_refused() -> u32 {
    let _: [(); 4] = [{
        unsafe {
            core::arch::asm!("");
        }
        return 7;
    }; 4];
    99
}

pub fn one() -> u32 {
    let mut n = 0;
    let _ = [{
        n += 1;
    }; 1];
    n
}

pub fn indexed_dynamic(index: usize) -> u32 {
    let mut n = 0;
    let units = [{
        n += 1;
    }; 4];
    let _ = units[{
        n += 2;
        index
    }];
    n
}

pub fn index_base_and_index() -> u32 {
    let mut n = 0;
    let _ = ([{
        n += 1;
    }; 4])[{
        n *= 2;
        3
    }];
    n
}

pub fn unit_oob() -> u32 {
    let units = [(); 4];
    let _ = units[4];
    7
}

pub fn unit_zero_index() -> u32 {
    let units = [(); 0];
    let _ = units[0];
    7
}

pub fn array_reassign_during_index() -> u32 {
    let mut units = [(); 4];
    let mut n = 0;
    let _ = units[{
        units = [{
            n += 1;
        }; 4];
        2
    }];
    n
}

pub fn rest() -> u32 {
    let mut n = 0;
    let units = [{
        n += 1;
    }; 4];
    let [_, middle @ .., _] = units;
    n * 10 + middle.len() as u32
}

pub fn local_slice_len() -> u32 {
    let mut n = 0;
    let units = [{
        n += 1;
    }; 4];
    let slice: &[()] = &units;
    n * 10 + slice.len() as u32
}

pub fn inline_slice_len() -> u32 {
    let mut n = 0;
    let slice: &[()] = &[{
        n += 1;
    }; 4];
    n * 10 + slice.len() as u32
}
