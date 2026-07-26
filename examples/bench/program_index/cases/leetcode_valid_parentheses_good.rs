// Program-index fixture: LeetCode-style valid-parentheses with stack guards.

fn valid_parentheses(input: &[u8; 6]) -> bool {
    const INPUT_LEN: usize = 6;
    const STACK_CAP: usize = 8;

    let mut stack = [0u8; 8];
    let mut depth = 0usize;
    let mut index = 0usize;

    while index < INPUT_LEN {
        let byte = input[index];
        if byte == b'(' {
            if depth == STACK_CAP {
                return false;
            }
            stack[depth] = byte;
            depth += 1;
        } else if byte == b')' {
            if depth == 0 {
                return false;
            }
            depth -= 1;
            let _ = stack[depth];
        }
        index += 1;
    }

    depth == 0
}

fn main() {
    let input = *b"(()())";
    let _ = valid_parentheses(&input);
}
