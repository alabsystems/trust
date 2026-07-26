use installed_serde_derive::{decode_message, encode_message};

fn main() {
    let message = decode_message(
        r#"{"sender":"Sanny","body":"Trust installed-toolchain fixture","priority":2}"#,
    )
    .expect("deserialize fixture message");
    println!("{}", encode_message(&message).expect("serialize fixture message"));
}
