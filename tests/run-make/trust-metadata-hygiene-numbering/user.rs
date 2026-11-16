fn main() {
    let x = hyg::twice!(7);
    assert_eq!(hyg::same(x, x), hyg::mix(7, 7));
    let mut v = [1u8, 2];
    hyg::later(&mut v);
    assert_eq!(v, [2, 1]);
}
