#include <stdint.h>
#include <stdio.h>
extern int8_t trust_c_i8_id(int8_t),trust_c_i8_not(int8_t),trust_c_i8_tail(int8_t);
extern int16_t trust_c_i16_id(int16_t),trust_c_i16_not(int16_t),trust_c_i16_tail(int16_t);
extern uint32_t observe_signed_w0(uintptr_t,uint64_t);
int main(void){
 for(uint32_t x=0;x<65536;++x){
  uint32_t narrow=(uint32_t)(int32_t)(int8_t)x;
  uint32_t wide=(uint32_t)(int32_t)(int16_t)x;
  uint64_t high=UINT64_C(0xdeadbeef00000000);
  uintptr_t fs[]={(uintptr_t)trust_c_i8_id,(uintptr_t)trust_c_i8_not,(uintptr_t)trust_c_i8_tail,(uintptr_t)trust_c_i16_id,(uintptr_t)trust_c_i16_not,(uintptr_t)trust_c_i16_tail};
  uint32_t in[]={narrow,narrow,narrow,wide,wide,wide};
  uint32_t expect[]={narrow,~narrow,~narrow,wide,~wide,~wide};
  for(unsigned f=0;f<6;++f){if(f<3&&x>=256)continue;
   uint32_t got=observe_signed_w0(fs[f],high|in[f]);
   if(got!=expect[f]){fprintf(stderr,"fn=%u rawX0=%016llx W0=%08x expected=%08x\n",f,(unsigned long long)(high|in[f]),got,expect[f]);return 1;}
  }
  if(trust_c_i8_id((int8_t)x)!=(int8_t)x||trust_c_i8_not((int8_t)x)!=(int8_t)~x||trust_c_i8_tail((int8_t)x)!=(int8_t)~x||trust_c_i16_id((int16_t)x)!=(int16_t)x||trust_c_i16_not((int16_t)x)!=(int16_t)~x||trust_c_i16_tail((int16_t)x)!=(int16_t)~x)return 2;
 }
#ifndef SKIP_SIGNED_STORES
 extern int8_t trust_c_i8_store(uint8_t*,uint64_t);
 extern int16_t trust_c_i16_store(uint8_t*,uint64_t);
 extern uint32_t observe_signed_store_w0(uintptr_t,uintptr_t,uint64_t);
 for(unsigned x=0;x<256;++x){
  uint8_t bytes[]={0xa5,0,0x5a};
  if(observe_signed_store_w0((uintptr_t)trust_c_i8_store,(uintptr_t)&bytes[1],x)!=(uint32_t)-7||bytes[0]!=0xa5||bytes[1]!=x||bytes[2]!=0x5a)return 3;
  if(observe_signed_store_w0((uintptr_t)trust_c_i16_store,(uintptr_t)&bytes[1],x)!=(uint32_t)-7||bytes[0]!=0xa5||bytes[1]!=x||bytes[2]!=0x5a)return 4;
  if(trust_c_i8_store(&bytes[1],x)!=-7||trust_c_i16_store(&bytes[1],x)!=-7||bytes[1]!=x)return 5;
 }
#endif
 puts("all signed8/16 legal W0 values and independent high32 passed");return 0;
}
