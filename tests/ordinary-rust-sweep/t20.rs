pub fn clamp_all(v: &mut [i32]) {
    for x in v.iter_mut() {
        if *x < 0 {
            *x = 0;
        }
    }
}
