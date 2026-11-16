#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern int64_t trust_stack_int(int64_t i0, int64_t i1, int64_t i2, int64_t i3, int64_t i4, int64_t i5, int64_t i6, int64_t i7, int8_t a, uint8_t b, int16_t c, uint16_t d, int32_t e, uint32_t f, int64_t g);
extern float trust_stack_f32(float f0, double f1, float f2, double f3, float f4, double f5, float f6, double f7, float x);
extern double trust_stack_f64(float f0, double f1, float f2, double f3, float f4, double f5, float f6, double f7, float x, double y);
extern double trust_stack_mixed(int64_t i0, float f0, int64_t i1, double f1, int64_t i2, float f2, int64_t i3, double f3, int64_t i4, float f4, int64_t i5, double f5, int64_t i6, float f6, int64_t i7, double f7, uint8_t a, float b, int16_t c, double d, uint32_t e, float f, int64_t g);
extern double trust_stack_outgoing(void);
extern int64_t trust_stack_local(void);

double original_stack_mixed(int64_t i0, float f0, int64_t i1, double f1, int64_t i2, float f2, int64_t i3, double f3, int64_t i4, float f4, int64_t i5, double f5, int64_t i6, float f6, int64_t i7, double f7, uint8_t a, float b, int16_t c, double d, uint32_t e, float f, int64_t g) {
    return i0 == 11 && f0 == 1.25f && i1 == -22 && f1 == -2.5 && i2 == 33 && f2 == 3.75f && i3 == -44 && f3 == -4.25 && i4 == 55 && f4 == 5.5f && i5 == -66 && f5 == -6.75 && i6 == 77 && f6 == 7.25f && i7 == -88 && f7 == -8.5 && a == 241 && b == -9.75f && c == -12345 && d == 17.5 && e == 4000000001 && f == 21.25f && g == 81985529216486895 ? 128.5 : -2.0;
}

int main(void) {
    const int64_t integers[] = { -97, 241, -12345, 54321, -123456789, 4000000001, 81985529216486895 };
    for (int i = 0; i < 7; ++i) {
        if (trust_stack_int(i, -22, 33, -44, 55, -66, 77, -88, -97, 241, -12345, 54321, -123456789, 4000000001, 81985529216486895) != integers[i]) return 10 + i;
    }
    const uint32_t bits32[] = {0, UINT32_C(0x80000000), UINT32_C(0x7f800000), UINT32_C(0xff800000), UINT32_C(0x7fc01234), 1, UINT32_C(0x3f800000)};
    const uint64_t bits64[] = {0, UINT64_C(0x8000000000000000), UINT64_C(0x7ff0000000000000), UINT64_C(0xfff0000000000000), UINT64_C(0x7ff8000012345678), 1, UINT64_C(0x3ff0000000000000)};
    for (unsigned i = 0; i < sizeof(bits32) / sizeof(bits32[0]); ++i) {
        float x, y; uint32_t got; memcpy(&x, &bits32[i], sizeof(x)); y = trust_stack_f32(1.25, -2.5, 3.75, -4.25, 5.5, -6.75, 7.25, -8.5, x); memcpy(&got, &y, sizeof(got));
        if (got != bits32[i]) return 20 + (int)i;
    }
    for (unsigned i = 0; i < sizeof(bits64) / sizeof(bits64[0]); ++i) {
        double x, y; uint64_t got; memcpy(&x, &bits64[i], sizeof(x)); y = trust_stack_f64(1.25, -2.5, 3.75, -4.25, 5.5, -6.75, 7.25, -8.5, 13.25f, x); memcpy(&got, &y, sizeof(got));
        if (got != bits64[i]) return 30 + (int)i;
    }
    if (trust_stack_mixed(11, 1.25, -22, -2.5, 33, 3.75, -44, -4.25, 55, 5.5, -66, -6.75, 77, 7.25, -88, -8.5, 241, -9.75, -12345, 17.5, 4000000001, 21.25, 81985529216486895) != 128.5) return 40;
    if (trust_stack_outgoing() != 128.5) return 41;
    if (trust_stack_local() != INT64_C(81985529216486895)) return 42;
    puts("source scalar stack, natural packing and independent register banks agree");
    return 0;
}
