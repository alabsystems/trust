#![crate_type = "lib"]
// SOUNDNESS REGRESSION (name-collision false proof, found by the adversarial false-proof
// hunt). The accumulator `t` in the inner block gets the sound bound `t <= 4*255 = 1020`,
// but the function PARAMETER is ALSO named `t` — a DISTINCT local. If the bound fact were
// keyed by the non-unique source name "t" (the bug), it would leak onto the parameter's
// `t + 60000` overflow check and vacuously prove it — a FALSE PROOF (param t can be 40000,
// 40000+60000 = 100000 > u16::MAX). place_to_var_name now disambiguates same-named distinct
// locals to a unique `_<local>` key, so the bound cannot leak: this stays NOT fully
// discharged (the `t + 60000` is correctly retained). If this ever becomes fully proved,
// the name-collision soundness hole has regressed.
pub fn f(t: u16) -> u16 {
    {
        let mut t: u16 = 0;
        for &x in &[255u8, 255, 255, 255] {
            t += x as u16;
        }
        let _ = t;
    }
    t + 60000
}
