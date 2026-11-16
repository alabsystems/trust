// Trust: the same minted definition is harmless while unused and must fail the
// native PURE gate when called or reified. An eager registry walk rejects both.
#![allow(dead_code)]

static mut STATE: u64 = 7;

#[cfg(not(pure))]
#[inline(never)]
fn read(_a: u64) -> u64 {
    unsafe { STATE }
}

#[cfg(pure)]
#[inline(never)]
fn read(a: u64) -> u64 {
    let local = a.wrapping_add(7);
    let reference = &local;
    let reborrow = &*reference;
    *reborrow
}

clean {
    def applyRead (a : UInt64) : UInt64 := read a
}

fn main() {
    #[cfg(call)]
    assert_eq!(applyRead(0), 7);

    #[cfg(address)]
    std::hint::black_box(applyRead as fn(u64) -> u64);

    #[cfg(type_only)]
    {
        let pointer: Option<fn(u64) -> u64> = None;
        std::hint::black_box(pointer);
    }

    #[cfg(frontend_error)]
    let _: MissingType;
}
