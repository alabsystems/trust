#include <stdint.h>
#include <stdio.h>

int32_t fill_through_ref(int32_t x, int32_t y);
int32_t read_through_ref(int32_t x, int32_t y);
uint32_t mixed_through_ref(uint32_t t, uint32_t v, uint32_t h);

static const int32_t INTS[] = {0, 1, -1, 7, 9, INT32_MIN, INT32_MAX, 0x12345678, -0x0f0f0f0f};
static const uint32_t TAGS[] = {0, 1, 0x7f, 0x80, 0xff, 0x1ff};
static const uint32_t WIDES[] = {0, 1, 0xdeadbeef, 0xffffffff, 0x80000000};
static const uint32_t HALVES[] = {0, 1, 0x7fff, 0x8000, 0xffff, 0x1ffff};

int main(void) {
    for (unsigned i = 0; i < sizeof INTS / sizeof INTS[0]; i++)
        for (unsigned j = 0; j < sizeof INTS / sizeof INTS[0]; j++)
            printf("fill %d %d %d\nread %d %d %d\n", INTS[i], INTS[j],
                   fill_through_ref(INTS[i], INTS[j]), INTS[i], INTS[j],
                   read_through_ref(INTS[i], INTS[j]));
    for (unsigned i = 0; i < sizeof TAGS / sizeof TAGS[0]; i++)
        for (unsigned j = 0; j < sizeof WIDES / sizeof WIDES[0]; j++)
            for (unsigned k = 0; k < sizeof HALVES / sizeof HALVES[0]; k++)
                printf("mixed %u %u %u %u\n", TAGS[i], WIDES[j], HALVES[k],
                       mixed_through_ref(TAGS[i], WIDES[j], HALVES[k]));
    return 0;
}
