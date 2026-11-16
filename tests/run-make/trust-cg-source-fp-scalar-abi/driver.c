#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern float trust_fp32_identity(float);
extern double trust_fp64_identity(double);
extern float trust_fp32_add(float);
extern double trust_fp64_add(double);
extern double trust_fp_mixed(int32_t, float, int64_t, double);
extern double trust_fp_banks(int64_t, float, int64_t, double, int64_t, float,
    int64_t, double, int64_t, float, int64_t, double, int64_t, float, int64_t, double);

double original_fp_mixed(int32_t a, float b, int64_t c, double d) {
    return a == -97 && b == -3.25f && c == INT64_C(0x123456789abcdef) && d == 17.5 ? 42.25 : -1.0;
}

double original_fp_banks(int64_t i0, float f0, int64_t i1, double f1,
    int64_t i2, float f2, int64_t i3, double f3, int64_t i4, float f4,
    int64_t i5, double f5, int64_t i6, float f6, int64_t i7, double f7) {
    return i0 == 11 && i1 == -22 && i2 == 33 && i3 == -44 && i4 == 55 && i5 == -66 && i6 == 77 && i7 == -88 &&
        f0 == 1.25f && f1 == -2.5 && f2 == 3.75f && f3 == -4.25 && f4 == 5.5f && f5 == -6.75 && f6 == 7.25f && f7 == -8.5 ? 128.5 : -2.0;
}

int main(void) {
    const uint32_t bits32[] = {0, UINT32_C(0x80000000), UINT32_C(0x7f800000), UINT32_C(0xff800000), UINT32_C(0x7fc01234), 1, UINT32_C(0x3f800000)};
    const uint64_t bits64[] = {0, UINT64_C(0x8000000000000000), UINT64_C(0x7ff0000000000000), UINT64_C(0xfff0000000000000), UINT64_C(0x7ff8000012345678), 1, UINT64_C(0x3ff0000000000000)};
    for (unsigned i = 0; i < sizeof(bits32) / sizeof(bits32[0]); ++i) {
        float x, y; uint32_t got; memcpy(&x, &bits32[i], sizeof(x)); y = trust_fp32_identity(x); memcpy(&got, &y, sizeof(got));
        if (got != bits32[i]) return 10 + (int)i;
    }
    for (unsigned i = 0; i < sizeof(bits64) / sizeof(bits64[0]); ++i) {
        double x, y; uint64_t got; memcpy(&x, &bits64[i], sizeof(x)); y = trust_fp64_identity(x); memcpy(&got, &y, sizeof(got));
        if (got != bits64[i]) return 20 + (int)i;
    }
    if (trust_fp32_add(-3.25f) != -2.0f || trust_fp64_add(17.5) != 20.0) return 30;
    if (trust_fp_mixed(-97, -3.25f, INT64_C(0x123456789abcdef), 17.5) != 42.25) return 31;
    if (trust_fp_banks(11, 1.25f, -22, -2.5, 33, 3.75f, -44, -4.25, 55, 5.5f, -66, -6.75, 77, 7.25f, -88, -8.5) != 128.5) return 32;
    puts("source f32/f64, Rust calls and mixed C register banks agree");
    return 0;
}
