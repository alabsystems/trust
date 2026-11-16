#![crate_type = "lib"]

#[repr(C)]
pub struct Header { pub marker: u8, pub size: u64, pub spare: u64 }
#[repr(C)]
pub struct Inner { pub prefix: u32, pub signed: i16 }
#[repr(C)]
pub struct Outer { pub prefix: u64, pub inner: Inner }
#[repr(C, packed)]
pub struct Packed { pub marker: u8, pub size: u64 }
#[repr(C)]
pub struct Float { pub value: f64 }

#[no_mangle]
pub unsafe extern "C" fn entry_field(p: *const Header) -> u64 { unsafe { (*p).size } }
#[no_mangle]
pub unsafe extern "C" fn retyped_field(p: *const u8) -> u64 { unsafe { (*(p as *const Header)).size } }
#[no_mangle]
pub unsafe extern "C" fn local_retyped(p: *const u8) -> u64 {
    let h = p as *const Header;
    unsafe { (*h).size }
}
#[no_mangle]
pub unsafe extern "C" fn nested_signed(p: *const u8) -> i16 { unsafe { (*(p as *const Outer)).inner.signed } }
#[no_mangle]
pub unsafe extern "C" fn read_after_store(p: *mut Header, value: u64) -> u64 {
    unsafe { (*p).size = value; (*p).size }
}
#[no_mangle]
pub unsafe extern "C" fn alias_after_store(p: *mut Header, q: *const Header, value: u64) -> u64 {
    unsafe { (*p).size = value; (*q).size }
}
#[no_mangle]
pub fn borrowed_control(p: &Header) -> u64 { p.size }

#[inline(never)]
pub fn identity(p: *const Header) -> *const Header { p }
#[no_mangle]
pub unsafe extern "C" fn integer_origin(address: usize) -> u64 { unsafe { (*(address as *const Header)).size } }
#[no_mangle]
pub unsafe extern "C" fn call_origin(p: *const Header) -> u64 { unsafe { (*identity(p)).size } }
#[no_mangle]
pub unsafe extern "C" fn derived_origin(p: *const Header) -> u64 { unsafe { (*p.add(1)).size } }
#[no_mangle]
pub unsafe extern "C" fn packed_field(p: *const Packed) -> u64 { unsafe { (*p).size } }
#[no_mangle]
pub unsafe extern "C" fn float_field(p: *const Float) -> f64 { unsafe { (*p).value } }
#[no_mangle]
pub fn retyped_address_integer(p: *const u8) -> usize { let h = p as *const Header; h as usize }
#[no_mangle]
pub unsafe fn borrowed_retype(p: &Header) -> u64 { unsafe { (*((p as *const Header) as *const u8 as *const Header)).size } }
#[no_mangle]
pub unsafe fn fat_origin(p: *const [u8]) -> u64 { unsafe { (*(p as *const Header)).size } }
