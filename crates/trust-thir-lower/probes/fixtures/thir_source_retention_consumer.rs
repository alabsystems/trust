extern crate thir_source_capture_upstream as up;
fn main(){let _=up::source_identity(());let _=up::source_typed_relay([1,2],());let _=up::source_value_chain(());let _=up::source_identity(13u64);let _=up::source_identity([1u8,2,3]);let _=up::source_identity([0u8;0]);
let _=up::source_identity(up::Packet{hi:5,lo:2});let referenced=23u64;let _=up::source_identity(&referenced);
let _=up::source_const_array::<u8,3>([1,2,3]);let _=up::source_const_array::<u16,5>([1,2,3,4,5]);let _=up::source_typed_relay([1,2],[3u64,4,5]);let _=up::root::<u8,3>(1);let _=up::root::<u16,5>(2);let _=up::source_chain::<u8,3>(4);let _=up::source_diamond::<u8,3>(4);}
