#![feature(never_type, extern_types, adt_const_params, unsized_const_params, f16, f128)]
#![allow(incomplete_features)]
extern crate legacy_site_fixture as upstream;
pub fn case_bool() -> u64 { upstream::typed::<bool>() }
pub fn case_char() -> u64 { upstream::typed::<char>() }
pub fn case_str() -> u64 { upstream::typed::<str>() }
pub fn case_never() -> u64 { upstream::typed::<!>() }
pub fn case_foreign() -> u64 { upstream::typed::<upstream::Opaque>() }
pub fn case_unit() -> u64 { upstream::typed::<()>() }
pub fn case_tuple() -> u64 { upstream::typed::<(u8,bool,char)>() }
pub fn case_array() -> u64 { upstream::typed::<[u16;3]>() }
pub fn case_slice() -> u64 { upstream::typed::<[u16]>() }
pub fn case_ref() -> u64 { upstream::typed::<&'static u64>() }
pub fn case_mut_ref() -> u64 { upstream::typed::<&'static mut u64>() }
pub fn case_raw() -> u64 { upstream::typed::<*const u64>() }
pub fn case_mut_raw() -> u64 { upstream::typed::<*mut u64>() }
pub fn case_nominal() -> u64 { upstream::typed::<upstream::Envelope<'static,u64,3>>() }
pub fn case_dyn() -> u64 { upstream::typed::<dyn upstream::Dyn<4,Assoc=u64> + Send>() }
pub fn case_fn() -> u64 { upstream::typed::<fn(u8)->u64>() }
pub fn case_unsafe_fn() -> u64 { upstream::typed::<unsafe fn(u8)->u64>() }
pub fn case_extern_c() -> u64 { upstream::typed::<extern "C" fn(u8)->u64>() }
pub fn case_extern_c_unsafe() -> u64 { upstream::typed::<unsafe extern "C" fn(u8)->u64>() }
pub fn case_extern_c_variadic() -> u64 { upstream::typed::<unsafe extern "C" fn(u64,...)->u64>() }
pub fn case_extern_c_unwind() -> u64 { upstream::typed::<extern "C-unwind" fn(u8)->u64>() }
pub fn case_isize() -> u64 { upstream::typed::<isize>() }
pub fn case_i8() -> u64 { upstream::typed::<i8>() }
pub fn case_i16() -> u64 { upstream::typed::<i16>() }
pub fn case_i32() -> u64 { upstream::typed::<i32>() }
pub fn case_i64() -> u64 { upstream::typed::<i64>() }
pub fn case_i128() -> u64 { upstream::typed::<i128>() }
pub fn case_usize() -> u64 { upstream::typed::<usize>() }
pub fn case_u8() -> u64 { upstream::typed::<u8>() }
pub fn case_u16() -> u64 { upstream::typed::<u16>() }
pub fn case_u32() -> u64 { upstream::typed::<u32>() }
pub fn case_u64() -> u64 { upstream::typed::<u64>() }
pub fn case_u128() -> u64 { upstream::typed::<u128>() }
pub fn case_f16() -> u64 { upstream::typed::<f16>() }
pub fn case_f32() -> u64 { upstream::typed::<f32>() }
pub fn case_f64() -> u64 { upstream::typed::<f64>() }
pub fn case_f128() -> u64 { upstream::typed::<f128>() }
pub fn case_value_const_1() -> u64 { upstream::const_only::<1>() }
pub fn case_value_const_2() -> u64 { upstream::const_only::<2>() }
pub fn case_value_bool() -> u64 { upstream::bool_only::<true>() }
pub fn case_value_char() -> u64 { upstream::char_only::<'é'>() }
pub fn case_value_aggregate() -> u64 { upstream::aggregate::<{upstream::Params{flag:true,pair:(3,65535)}}>() }
pub fn case_value_const_array() -> u64 { upstream::array::<{[3,65535]}>() }
pub fn case_value_const_tuple() -> u64 { upstream::tuple::<{(7,true)}>() }
pub fn case_value_text() -> u64 { upstream::text::<"hé">() }
fn item(_:u8)->u64{7}
pub fn case_infer_item() -> u64 { upstream::infer(item) }
pub fn case_infer_closure() -> u64 { upstream::infer(||7u64) }
pub fn case_infer_coroutine() -> u64 { upstream::infer(async {7u64}) }
pub fn case_infer_coroutine_closure() -> u64 { upstream::infer(async ||7u64) }
