#![crate_type = "lib"]
// Exhaustive by-value enum match. `match o { Some(v) => v, None => 0 }` desugars
// to a `SwitchInt` on the Option discriminant whose `otherwise` arm is a
// compiler-certified `Unreachable` block. The native CHC now PROVES that arm
// infeasible — the discriminant of a validly-constructed Option is in {0,1} — and
// the body is panic-free, so the whole function is statically panic-free under
// the default strict policy. Exercises the slice/enum-match lane end to end:
// discriminant-validity assume, precise boolean `Or`, tracked-aggregate field
// extraction of the Option parameter, and `Unreachable`-as-proof-obligation.
pub fn match_exhaustive_enum(o: Option<i32>) -> i32 {
    match o {
        Some(v) => v,
        None => 0,
    }
}
