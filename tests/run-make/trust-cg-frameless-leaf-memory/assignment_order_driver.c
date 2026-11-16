#include <stdint.h>
extern uint64_t raw_store_rhs_order(uint8_t *, uint8_t *, uint64_t);
extern uint64_t raw_field_rhs_order(void *, void *, uint64_t);
int main(void) {
    for (unsigned value = 0; value < 256; ++value) {
        uint8_t old[3] = {19, 23, 29}, replacement[3] = {31, 37, 41};
        if (raw_store_rhs_order(old, replacement, value) != 0 ||
            old[0] != 19 || old[1] != 23 || old[2] != 29 ||
            replacement[0] != value || replacement[1] != 37 || replacement[2] != 41) return 1;
        if (raw_field_rhs_order(old, replacement, value) != 0 ||
            old[0] != 19 || old[1] != 23 || old[2] != 29 ||
            replacement[0] != value || replacement[1] != value || replacement[2] != 41) return 2;
    }
    return 0;
}
