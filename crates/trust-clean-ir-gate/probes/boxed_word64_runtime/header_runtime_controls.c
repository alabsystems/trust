/* Copyright 2026 Andrew Yates | Apache-2.0
 * Finite observations of the actual included runtime; no C/ARC/NoUB proof.
 * Copy the unchanged runtime source+header into runtime/{src,include} first.
 */
#include "runtime/src/clean_runtime.c"

int main(void) {
    const uint32_t cases[] = {0, 1, 2, UINT32_C(0xDFFFFFFF), UINT32_C(0xE0000000),
                             UINT32_C(0xE8000000), UINT32_C(0xEFFFFFFF),
                             UINT32_C(0xF0000000), UINT32_MAX};
    for (size_t i = 0; i < sizeof(cases) / sizeof(cases[0]); ++i) {
        uint32_t before = cases[i];
        clean_obj* o = clean_box_uint64(UINT64_C(0xFEDCBA9876543210));
        atomic_store_explicit(&o->header.ref_count, before, memory_order_relaxed);
        bool final = clean_rc_drop(o);
        uint32_t after = atomic_load_explicit(&o->header.ref_count, memory_order_relaxed);
        uint32_t expected = before >= UINT32_C(0xE0000000) ? before : before - UINT32_C(1);
        if (final != (before == 0) || after != expected) return 10;
        /* This probes drop's uint32 update only; it never pretends the
         * transient wrapped last-reference header is a live owned budget. */
        free(o);
        o = clean_box_uint64(7);
        atomic_store_explicit(&o->header.ref_count, before, memory_order_relaxed);
        clean_inc(o);
        after = atomic_load_explicit(&o->header.ref_count, memory_order_relaxed);
        expected = before < UINT32_C(0xF0000000) ? before + UINT32_C(1) : before;
        if (after != expected) return 20;
        free(o);
        o = clean_box_uint64(7);
        atomic_store_explicit(&o->header.ref_count, before, memory_order_relaxed);
        clean_inc_n(o, 1);
        after = atomic_load_explicit(&o->header.ref_count, memory_order_relaxed);
        if (after != expected) return 30;
        free(o);
    }
    const uint64_t words[] = {0, 1, UINT64_C(0x8000000000000000),
                              UINT64_C(0xFEDCBA9876543210), UINT64_MAX};
    for (size_t i = 0; i < sizeof(words) / sizeof(words[0]); ++i) {
        clean_obj* o = clean_box_uint64(words[i]);
        if (atomic_load_explicit(&o->header.ref_count, memory_order_relaxed) != 0) return 40;
        clean_inc(o); /* Acquire the second owned argument before aliasing. */
        if (atomic_load_explicit(&o->header.ref_count, memory_order_relaxed) != 1) return 41;
        uint64_t a = clean_unbox_uint64(o), b = clean_unbox_uint64(o);
        clean_dec(o);
        if (a != words[i] || b != words[i] || clean_unbox_uint64(o) != words[i] ||
            atomic_load_explicit(&o->header.ref_count, memory_order_relaxed) != 0) return 42;
        clean_dec(o); /* No dereference after this last owned reference. */
    }
    return 0;
}
