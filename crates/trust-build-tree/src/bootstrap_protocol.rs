//! Support declaration only. Actual original fixed/GNU/Manager custody is
//! independently required; these bytes grant no scheduling or runtime rights.

pub const BOOTSTRAP_FIXED_PROTOCOL_MARKER: [u8; 64] = marker();
const fn marker() -> [u8; 64] {
    let mut output = [0; 64];
    let magic = *b"TRUSTBTFIX000001";
    let mut index = 0;
    while index < 16 {
        output[index] = magic[index];
        index += 1;
    }
    // Version, original fixed capture, same GNU, pre-Step jobs cap, no Host,
    // no completed-runtime protocol.
    let fields = [1u64, 1, 1, 1, 0, 0];
    let mut field = 0;
    while field < fields.len() {
        let bytes = fields[field].to_be_bytes();
        let mut byte = 0;
        while byte < 8 {
            output[16 + field * 8 + byte] = bytes[byte];
            byte += 1;
        }
        field += 1;
    }
    output
}
