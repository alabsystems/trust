use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Message {
    pub sender: String,
    pub body: String,
    pub priority: u8,
}

pub fn decode_message(input: &str) -> Result<Message, serde_json::Error> {
    serde_json::from_str(input)
}

pub fn encode_message(message: &Message) -> Result<String, serde_json::Error> {
    serde_json::to_string(message)
}

#[cfg(test)]
mod tests {
    use super::{Message, decode_message, encode_message};

    #[test]
    fn serde_derive_round_trips_a_message() {
        let expected = Message {
            sender: "Sanny".into(),
            body: "Trust installed-toolchain fixture".into(),
            priority: 2,
        };
        let encoded = encode_message(&expected).expect("serialize fixture message");
        let decoded = decode_message(&encoded).expect("deserialize fixture message");
        assert_eq!(decoded, expected);
    }
}
