#include <stdint.h>
extern uint32_t canary_0(void);
extern uint32_t canary_1(void);
extern uint32_t canary_2(void);
extern uint32_t canary_3(void);
extern uint64_t once_argument(uint64_t);
extern uint64_t once_receiver_expression_order(void);
int main(void) {
 const uint64_t xs[]={0,1,7,8,UINT64_MAX,UINT64_C(0x8000000000000000)};
 for(unsigned i=0;i<sizeof(xs)/sizeof(xs[0]);++i)
   if(once_argument(xs[i])!=(xs[i]^UINT64_C(7))) return 1;
 if(once_receiver_expression_order()!=1212) return 1;
 return canary_0()!=41 || canary_1()!=141 || canary_2()!=43 || canary_3()!=47;
}
