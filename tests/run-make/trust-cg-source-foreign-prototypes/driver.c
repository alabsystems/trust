#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>

int32_t original_foreign_fixed(int8_t signed_value, uint16_t unsigned_value) {
    return signed_value == -101 && unsigned_value == UINT16_C(0xfedc) ? 0x10203 : -1;
}

int32_t original_foreign_variadic(int32_t tag, ...) {
    va_list args;
    va_start(args, tag);
    int32_t integer = va_arg(args, int);
    double floating = va_arg(args, double);
    uint64_t wide = va_arg(args, uint64_t);
    va_end(args);
    return tag == 97 && integer == -123 && floating == 17.5 &&
           wide == UINT64_C(0xfedcba9876543210) ? 0x40506 : -2;
}

extern int32_t trust_foreign_fixed(void);
extern int32_t trust_foreign_variadic(int32_t);
int main(void) {
    int32_t fixed = trust_foreign_fixed();
    int32_t variadic = trust_foreign_variadic(97);
    if (fixed != 0x10203 || variadic != 0x40506) {
        fprintf(stderr, "foreign ABI mismatch fixed=%d variadic=%d\n", fixed, variadic);
        return 1;
    }
    puts("source fixed and mixed variadic foreign calls agree");
    return 0;
}
