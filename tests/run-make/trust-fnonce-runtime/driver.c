#include <stdint.h>
#include <stdio.h>

extern uint64_t closure_write(uint64_t *, uint8_t);
extern uint64_t *closure_return(uint64_t *);

int main(void) {
    /* Trust: include 128..255 to catch a signed C argument extension. */
    for (unsigned delta = 0; delta <= UINT8_MAX; ++delta) {
        const uint64_t before = UINT64_C(0x123456789abcdef0);
        const uint64_t after = UINT64_C(0xfedcba9876543210);
        const uint64_t initial = UINT64_C(0x100000000) + 257 * (uint64_t)delta;
        uint64_t cells[] = {before, initial, after};
        const uint64_t expected = initial + delta;
        if (closure_write(&cells[1], (uint8_t)delta) != expected) return 1;
        if (cells[1] != expected) return 2;
        if (cells[0] != before || cells[2] != after) return 3;

        uint64_t *returned = closure_return(&cells[1]);
        if (returned != &cells[1]) return 4;
        *returned = expected ^ UINT64_C(0x5a5a5a5a5a5a5a5a);
        if (cells[1] != (expected ^ UINT64_C(0x5a5a5a5a5a5a5a5a))) return 5;
        if (cells[0] != before || cells[2] != after) return 6;
    }
    puts("fn_once pointer and store preserved");
    return 0;
}
