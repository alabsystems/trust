/* F1 hook: a FOREIGN main for the trust-cg object built from f1_lib.rs's trust-ir spelling. */
#include <stdint.h>
#include <stdio.h>
extern uint64_t parta_f1_program(void);
int main(void) {
    printf("%llu\n", (unsigned long long)parta_f1_program());
    return 0;
}
