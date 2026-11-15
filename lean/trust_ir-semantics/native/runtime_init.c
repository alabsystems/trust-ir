/* Copyright 2026 Andrew Yates | Apache-2.0
 * Native-only attachment. This C initializer and its correspondence are UNPROVED.
 * Lean's normal module-import initialization calls this exported module symbol.
 */
#include <lean/lean.h>
#include <stdint.h>

#ifndef TRUST_IR_ATTACHMENT_INITIALIZER
#define TRUST_IR_ATTACHMENT_INITIALIZER initialize_TrustIrNativeLink
#endif
#ifndef TRUST_IR_PROVIDER_INITIALIZER
#define TRUST_IR_PROVIDER_INITIALIZER initialize_TrustIrRuntime
#endif
#ifdef TRUST_IR_LEAN430
#define TRUST_IR_INIT_WORLD_DECL
#define TRUST_IR_INIT_WORLD_ARG
#else
#define TRUST_IR_INIT_WORLD_DECL , lean_object* world
#define TRUST_IR_INIT_WORLD_ARG , world
#endif

LEAN_EXPORT lean_object* TRUST_IR_PROVIDER_INITIALIZER(uint8_t builtin TRUST_IR_INIT_WORLD_DECL);
static uint8_t initialization_state = 0;
static lean_object* initialization_failure = NULL;

LEAN_EXPORT lean_object* TRUST_IR_ATTACHMENT_INITIALIZER(uint8_t builtin TRUST_IR_INIT_WORLD_DECL) {
    if (initialization_state == 2) return lean_io_result_mk_ok(lean_box(0));
    if (initialization_state == 3) {
        lean_inc(initialization_failure);
        return initialization_failure;
    }
    if (initialization_state == 1)
        return lean_io_result_mk_error(lean_mk_io_user_error(
            lean_mk_string("recursive TrustIr runtime initialization")));
    initialization_state = 1;
    lean_object* result = TRUST_IR_PROVIDER_INITIALIZER(builtin TRUST_IR_INIT_WORLD_ARG);
    if (lean_io_result_is_error(result)) {
        initialization_failure = result;
        lean_inc(initialization_failure);
        initialization_state = 3;
        return result;
    }
    initialization_state = 2;
    return result;
}
