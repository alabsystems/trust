-- Copyright 2026 Andrew Yates | Apache-2.0
import C11HeaderDeclarations
namespace C11ActualDeclarationData
open C11HeaderDeclarations C11HeaderTyping
def uint8_t_0 : String := "typedef unsigned char uint8_t;"
def uint16_t_0 : String := "typedef unsigned short uint16_t;"
def uint32_t_0 : String := "typedef unsigned int uint32_t;"
def clean_obj_header_0 : String := "typedef struct clean_obj_header {\n    _Atomic uint32_t ref_count;\n    uint8_t tag;\n    uint8_t kind;\n    uint8_t num_objs;   /* was uint16_t — now u8 matching Lean 4 m_other (Part of #1990) */\n    uint8_t scalar_sz;  /* bytes of scalar payload after object pointers (Part of #1990) */\n} clean_obj_header;"
def clean_obj_0 : String := "typedef struct clean_obj {\n    clean_obj_header header;\n    /* Object fields follow:\n     * - Object pointers first (num_objs count)\n     * - Scalar fields after (size varies by constructor)\n     */\n    struct clean_obj* fields[];\n} clean_obj;"
def CLEAN_RC_STICKY_DROP_0 : String := "#define CLEAN_RC_STICKY_DROP 0xE0000000u\n"
def CLEAN_RC_STICKY_0 : String := "#define CLEAN_RC_STICKY      0xF0000000u\n"
def bool_0 : String := "#define bool _Bool\n"
def true_0 : String := "#define true 1\n"
def false_0 : String := "#define false 0\n"
def bool_1 : String := "#define bool bool\n"
def false_1 : String := "#define false false\n"
def true_1 : String := "#define true true\n"
def atomic_thread_fence_0 : String := "#define atomic_thread_fence(order) __c11_atomic_thread_fence(order)\n"
def atomic_load_explicit_0 : String := "#define atomic_load_explicit __c11_atomic_load\n"
def atomic_fetch_add_explicit_0 : String := "#define atomic_fetch_add_explicit __c11_atomic_fetch_add\n"
def atomic_fetch_sub_explicit_0 : String := "#define atomic_fetch_sub_explicit __c11_atomic_fetch_sub\n"
end C11ActualDeclarationData
