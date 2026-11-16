#include <stdint.h>
#include <stdio.h>

extern uint64_t ordinary_constant(void);
extern uint64_t ordinary_identity(uint64_t);
extern uint64_t ordinary_helper_call(uint64_t);
extern uint8_t ordinary_c_byte(uint8_t);
extern uint32_t observe_ordinary_c_byte_w0(uint8_t);
extern uint32_t observe_ordinary_c_byte_raw_w0(uint64_t);
extern uint32_t observe_bad_byte_w0(uint8_t);
extern uint16_t ordinary_wide_byte(uint16_t);
extern uint32_t observe_ordinary_wide_byte_raw_w0(uint64_t);
extern void *ordinary_raw_pointer(void *);
extern int8_t ordinary_signed_byte(int8_t);
extern uint32_t observe_ordinary_signed_byte_raw_w0(uint64_t);

static int scalars(uint64_t value) {
    void *pointer = (void *)(uintptr_t)value;
    if ((uint64_t)(uintptr_t)ordinary_raw_pointer(pointer) != value) {
        fprintf(stderr, "full64 raw pointer transport disagrees for %016llx\n", (unsigned long long)value);
        return 1;
    }
    if (ordinary_constant() != 37 || ordinary_identity(value) != value ||
        ordinary_helper_call(value) != (value ^ UINT64_C(0x5a))) {
        fprintf(stderr, "full64 scalar result disagrees for %016llx\n", (unsigned long long)value);
        return 1;
    }
    return 0;
}

int main(void) {
    const uint64_t wide[] = {
        UINT64_C(256), UINT64_C(0xffffffff), UINT64_C(0x100000000),
        UINT64_C(0x8000000000000000), UINT64_C(0xffffffffffffffff),
        UINT64_C(0xdeadbeef00000080), UINT64_C(0x0123456789abcdef),
    };
    for (unsigned i = 0; i < sizeof(wide) / sizeof(wide[0]); ++i)
        if (scalars(wide[i])) return 1;
    for (uint32_t value = 0; value < 256; ++value) {
        if (scalars(value)) return 1;
        const uint32_t signed_value = (uint32_t)(int32_t)(int8_t)value;
        if (ordinary_signed_byte((int8_t)value) != (int8_t)value ||
            observe_ordinary_signed_byte_raw_w0(UINT64_C(0xdeadbeef00000000) | signed_value) != signed_value)
            return 1;
        const uint32_t expected = value ^ 0x5au;
        const uint8_t byte = (uint8_t)value;
        if ((uint32_t)ordinary_c_byte(byte) != expected || observe_ordinary_c_byte_w0(byte) != expected) {
            fprintf(stderr, "C byte/fullW0 mismatch for %u\n", value);
            return 1;
        }
        // Legal C-u8 W0 bits are constrained; incoming X0[63:32] stays free.
        const uint64_t high[] = {UINT64_C(0), UINT64_C(0xdeadbeef00000000), UINT64_C(0xffffffff00000000)};
        for (unsigned i = 0; i < sizeof(high) / sizeof(high[0]); ++i) {
            const uint32_t actual = observe_ordinary_c_byte_raw_w0(high[i] | value);
            if (actual != expected) {
                fprintf(stderr, "raw legal input %016llx: W0=%08x expected=%08x\n",
                        (unsigned long long)(high[i] | value), actual, expected);
                return 1;
            }
        }
        // The hand-authored observer discriminator has the correct low byte
        // and deliberately wrong high W0 bits. A byte-only observer must fail.
        const uint32_t bad = observe_bad_byte_w0(byte);
        if ((bad & 255u) != expected || bad == expected) {
            fprintf(stderr, "wholeW0 discriminator was accidentally narrowed\n");
            return 1;
        }
    }
    // Keep this fixture's original u16 identity source in the corpus as its
    // capability advances. The dedicated u16 fixture runs the full value sweep.
    const uint16_t words[] = {0, 1, 255, 256, 32767, 32768, 65534, 65535};
    const uint64_t high[] = {UINT64_C(0), UINT64_C(0xdeadbeef00000000), UINT64_C(0xffffffff00000000)};
    for (unsigned i = 0; i < sizeof(words) / sizeof(words[0]); ++i) {
        if (ordinary_wide_byte(words[i]) != words[i]) return 1;
        for (unsigned j = 0; j < sizeof(high) / sizeof(high[0]); ++j) {
            const uint32_t actual = observe_ordinary_wide_byte_raw_w0(high[j] | words[i]);
            if (actual != words[i]) {
                fprintf(stderr, "C-u16 fullW0 mismatch: value=%u actual=%08x\n", (unsigned)words[i], actual);
                return 1;
            }
        }
    }
    puts("native source routes: full64 and all 256 C-u8 W0 cases PASS; C-u16 W0 boundary cases PASS; raw pointer full64/null transport PASS");
    return 0;
}
