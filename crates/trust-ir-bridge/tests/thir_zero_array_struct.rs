// Trust: execute the direct producer's actual pure admission predicate without
// requiring a second rustc-private compiler cohort or duplicating its logic.
#[path = "../../trust-thir-lower/src/crate_module/zero_array_struct.rs"]
mod zero_array_struct;
