#include <stdint.h>

extern uint32_t thin_same_home(void);
extern uint32_t thin_different_homes(void);
extern uint32_t thin_effect_order(void);
extern uint32_t thin_unrelated_eq(void);

int main(void) {
    if (thin_same_home() != 1) return 1;
    if (thin_different_homes() != 0) return 2;
    /* Callee then both arguments, each once: 1,2,3 followed by true. */
    if (thin_effect_order() != 1231) return 3;
    /* Same spelling is not the authenticated core source identity. */
    if (thin_unrelated_eq() != 0) return 4;
    return 0;
}
