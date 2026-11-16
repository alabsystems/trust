.text
.globl _observe_signed_w0
_observe_signed_w0:
 stp x29,x30,[sp,#-16]!
 mov x29,sp
 mov x16,x0
 mov x0,x1
 blr x16
 ldp x29,x30,[sp],#16
 ret

.globl _observe_signed_store_w0
_observe_signed_store_w0:
 stp x29,x30,[sp,#-16]!
 mov x29,sp
 mov x16,x0
 mov x0,x1
 mov x1,x2
 blr x16
 ldp x29,x30,[sp],#16
 ret
