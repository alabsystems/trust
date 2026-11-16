#include <stdint.h>
extern uint64_t leaf_store(uint8_t *, uint64_t);
extern uint64_t leaf_load(const uint8_t *);
extern uint64_t leaf_copy(uint8_t *, const uint8_t *);
extern uint64_t leaf_gep(void *, uint64_t);
int main(void) {
    for (unsigned value=0;value<256;value++) {
        uint8_t bytes[3]={19,23,29}, expected[3]={(uint8_t)value,23,29};
        if (leaf_store(bytes,value)!=0 || bytes[0]!=expected[0] || bytes[1]!=23 || bytes[2]!=29) return 1;
        if (leaf_load(bytes)!=value) return 2;
        if (leaf_copy(bytes+1,bytes)!=0 || bytes[0]!=value || bytes[1]!=value || bytes[2]!=29) return 3;
        if (leaf_copy(bytes,bytes)!=0 || bytes[0]!=value || bytes[1]!=value || bytes[2]!=29) return 4;
        if (leaf_gep(bytes,value^0xa5)!=0 || bytes[0]!=value || bytes[1]!=(value^0xa5) || bytes[2]!=29) return 5;
    }
    return 0;
}
