// `transmutes_to_check` is consumed after HIR typeck and is not serialized by
// the witness grammar. A valid transmute root therefore must cold-typecheck;
// replay may not install the decoder's empty default for that list.
pub fn transmute_u32(x: u32) -> [u8; 4] {
    unsafe { core::mem::transmute(x) }
}
