
#include <stdint.h>
#include <stdio.h>
extern uint16_t trust_c_u16_id(uint16_t), trust_c_u16_not(uint16_t), trust_c_u16_xor(uint16_t), trust_c_u16_constant(uint16_t);
extern uint16_t trust_c_u16_trunc(uint32_t), trust_c_u16_rust_typed_not(uint16_t);
extern uint32_t observe_id_w0(uint16_t), observe_not_w0(uint16_t), observe_xor_w0(uint16_t), observe_constant_w0(uint16_t), observe_trunc_w0(uint32_t);
extern uint32_t observe_rust_typed_not_w0(uint16_t);
extern uint32_t observe_raw_id_w0(uint64_t), observe_raw_not_w0(uint64_t);
#define CHECK(actual,expected) do { uint32_t a=(actual), e=(expected); if(a!=e) { fprintf(stderr,"%s: W0=%08x expected=%08x input=%08x\n",#actual,a,e,x); return 1; } } while(0)
int main(void) {
  for (uint32_t x=0; x<65536; ++x) {
    uint16_t byte=(uint16_t)x;
    CHECK(trust_c_u16_id(byte),x); CHECK(observe_id_w0(byte),x);
    CHECK(trust_c_u16_not(byte),x^65535u); CHECK(observe_not_w0(byte),x^65535u);
    CHECK(trust_c_u16_rust_typed_not(byte),x^65535u); CHECK(observe_rust_typed_not_w0(byte),x^65535u);
    CHECK(trust_c_u16_xor(byte),x^42435u); CHECK(observe_xor_w0(byte),x^42435u);
    CHECK(trust_c_u16_constant(byte),40561u); CHECK(observe_constant_w0(byte),40561u);
    /* Legal small-argument contract constrains W0, not X0's upper32 bits. */
    uint64_t raw=UINT64_C(0xdeadbeef00000000)|x;
    CHECK(observe_raw_id_w0(raw),x); CHECK(observe_raw_not_w0(raw),x^65535u);
    uint32_t wide=UINT32_C(0xa5c30000)|x;
    CHECK(trust_c_u16_trunc(wide),x); CHECK(observe_trunc_w0(wide),x);
  }
  return 0;
}
