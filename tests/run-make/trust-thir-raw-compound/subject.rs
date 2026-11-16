#![crate_type="lib"]
#[repr(C)] pub struct Header { pub tag:u8, pub size:u64, pub spare:u64 }
#[repr(C)] pub struct Outer { pub prefix:u64, pub inner:Header }
#[repr(C,packed)] pub struct Packed { pub tag:u8, pub size:u64 }
#[no_mangle] pub unsafe extern "C" fn scalar_update(p:*mut u64,v:u64) { unsafe { *p ^= v; } }
#[no_mangle] pub unsafe extern "C" fn header_update(p:*mut Header,v:u64) { unsafe { (*p).size += v; } }
#[no_mangle] pub unsafe extern "C" fn nested_update(p:*mut Outer,v:u64) { unsafe { (*p).inner.size ^= v; } }
#[no_mangle] pub unsafe extern "C" fn rhs_update(p:*mut Header,v:u64) { unsafe { (*p).size += { (*p).size = v; 3 }; } }
#[no_mangle] pub unsafe extern "C" fn reassign_update(mut p:*mut Header,q:*mut Header,v:u64) { unsafe { (*p).size ^= { p=q; v }; } }
#[no_mangle] pub unsafe extern "C" fn shift_update(p:*mut Header,v:u8) { unsafe { (*p).size <<= v; } }
#[no_mangle] pub unsafe extern "C" fn header_store(p:*mut Header,v:u64) { unsafe { (*p).size = v; } }
#[no_mangle] pub unsafe extern "C" fn derived_update(p:*mut Header,v:u64) { unsafe { (*p.add(1)).size ^= v; } }
#[no_mangle] pub unsafe extern "C" fn float_update(p:*mut f64,v:f64) { unsafe { *p += v; } }

#[no_mangle]
pub unsafe extern "C" fn packed_update(p: *mut Packed, v: u64) {
    unsafe { (*p).size += v; }
}
