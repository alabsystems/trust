#include <stdint.h>
extern uint32_t *leaf_source_anchor(uint32_t *);
int main(void) {
    uint32_t values[16];
    for (unsigned i=0;i<16;++i) values[i]=17+i;
    for (unsigned i=0;i<16;++i)
        if (leaf_source_anchor(&values[i])!=&values[i] || values[i]!=17+i) return 1;
    return 0;
}
