// WS7.11 (F-114): drive `sel` over its boundary vectors and print one line per
// vector, `a b sel(a, b)` in decimal. The recipe links this SAME file against
// the trust-cg (F1, strict gate) object and the LLVM object and compares both
// outputs with the values the recipe computes itself.
#include <stdint.h>
#include <stdio.h>

extern uint64_t sel(uint64_t a, uint64_t b);

int main(void) {
    static const uint64_t vectors[][2] = {
        /* a == b: the then-arm runs and must flip bit 0 */
        {5, 5},
        {0, 0},
        /* a == b == u64::MAX: the then-arm at the top of the range */
        {UINT64_MAX, UINT64_MAX},
        {0x8000000000000000ull, 0x8000000000000000ull},
        /* a != b: the else-arm returns b unchanged */
        {1, 2},
        {7, 6},
        {UINT64_MAX, 0},
        {0, UINT64_MAX},
        /* differ only in bit 0, the bit the then-arm flips */
        {4, 5},
        /* differ only above 32 bits: a 32-bit compare would take the wrong arm */
        {0x100000005ull, 5},
    };
    for (unsigned i = 0; i < sizeof vectors / sizeof vectors[0]; i++) {
        uint64_t a = vectors[i][0];
        uint64_t b = vectors[i][1];
        printf("%llu %llu %llu\n", (unsigned long long)a, (unsigned long long)b,
               (unsigned long long)sel(a, b));
    }
    return 0;
}
