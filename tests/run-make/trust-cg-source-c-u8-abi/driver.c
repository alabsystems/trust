
#include <stdint.h>
#include <stdio.h>
extern uint8_t trust_c_u8_id(uint8_t), trust_c_u8_not(uint8_t), trust_c_u8_xor(uint8_t), trust_c_u8_constant(uint8_t);
extern uint8_t trust_c_u8_trunc(uint32_t), trust_c_u8_rust_typed_not(uint8_t);
extern uint32_t observe_id_w0(uint8_t), observe_not_w0(uint8_t), observe_xor_w0(uint8_t), observe_constant_w0(uint8_t), observe_trunc_w0(uint32_t);
extern uint32_t observe_rust_typed_not_w0(uint8_t);
extern uint32_t observe_raw_id_w0(uint64_t), observe_raw_not_w0(uint64_t);
#define CHECK(actual,expected) do { uint32_t a=(actual), e=(expected); if(a!=e) { fprintf(stderr,"%s: W0=%08x expected=%08x input=%08x\n",#actual,a,e,x); return 1; } } while(0)
int main(void) {
  for (uint32_t x=0; x<256; ++x) {
    uint8_t byte=(uint8_t)x;
    CHECK(trust_c_u8_id(byte),x); CHECK(observe_id_w0(byte),x);
    CHECK(trust_c_u8_not(byte),x^255u); CHECK(observe_not_w0(byte),x^255u);
    CHECK(trust_c_u8_rust_typed_not(byte),x^255u); CHECK(observe_rust_typed_not_w0(byte),x^255u);
    CHECK(trust_c_u8_xor(byte),x^165u); CHECK(observe_xor_w0(byte),x^165u);
    CHECK(trust_c_u8_constant(byte),211u); CHECK(observe_constant_w0(byte),211u);
    /* Legal small-argument contract constrains W0, not X0's upper32 bits. */
    uint64_t raw=UINT64_C(0xdeadbeef00000000)|x;
    CHECK(observe_raw_id_w0(raw),x); CHECK(observe_raw_not_w0(raw),x^255u);
    uint32_t wide=UINT32_C(0xa5c39e00)|x;
    CHECK(trust_c_u8_trunc(wide),x); CHECK(observe_trunc_w0(wide),x);
  }
  return 0;
}
