// Program-index fixture: LeetCode-style valid-parentheses missing pop guards.
//
// The sample main is balanced, but the helper underflows depth for a caller
// that starts with a closing parenthesis.

fn valid_parentheses_unchecked(input: &[u8; 6]) -> bool {
    const INPUT_LEN: usize = 6;

    let mut stack = [0u8; 8];
    let mut depth = 0usize;
    let mut index = 0usize;

    while index < INPUT_LEN {
        let byte = input[index];
        if byte == b'(' {
            stack[depth] = byte;
            depth += 1;
        } else if byte == b')' {
            depth -= 1;
            let _ = stack[depth];
        }
        index += 1;
    }

    depth == 0
}

fn main() {
    let input = *b"(()())";
    let _ = valid_parentheses_unchecked(&input);
}
