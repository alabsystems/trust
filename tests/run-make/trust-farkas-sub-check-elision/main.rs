extern crate subtraction;

fn main() {
    #[cfg(not(twin))]
    let input = [0u8; 6];
    #[cfg(twin)]
    let input = [0u8; 5];
    println!("{:?}", subtraction::subtract(std::hint::black_box(&input)));
}
