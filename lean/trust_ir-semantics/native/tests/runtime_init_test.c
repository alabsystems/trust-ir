/* Copyright 2026 Andrew Yates | Apache-2.0
 * Actual Lean IO results with a synthetic provider; source lifecycle controls only.
 */
#include <lean/lean.h>
#include <stdint.h>
#include "../runtime_init.c"

static lean_object* control_marker(lean_object* unit) { (void)unit; return lean_box(0); }
#define STRINGIFY_INNER(x) #x
#define STRINGIFY(x) STRINGIFY_INNER(x)

static unsigned calls = 0;
static uint8_t observed_builtin = 0;
static lean_object* observed_world = NULL;
LEAN_EXPORT lean_object* TRUST_IR_PROVIDER_INITIALIZER(uint8_t builtin TRUST_IR_INIT_WORLD_DECL) {
    calls++;
    observed_builtin = builtin;
#ifndef TRUST_IR_LEAN430
    observed_world = world;
#endif
#if TEST_MODE == 1
    if (calls == 1) return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("owned injected init error")));
#elif TEST_MODE == 2
    return TRUST_IR_ATTACHMENT_INITIALIZER(builtin TRUST_IR_INIT_WORLD_ARG);
#endif
    return lean_io_result_mk_ok(lean_box(0));
}
extern void lean_initialize_runtime_module(void);
extern lean_object* initialize_Init(uint8_t builtin TRUST_IR_INIT_WORLD_DECL);
int main(void) {
    lean_initialize_runtime_module();
    lean_object* base = initialize_Init(1
#ifndef TRUST_IR_LEAN430
        , lean_io_mk_world()
#endif
    );
    if (lean_io_result_is_error(base)) return 71;
    lean_dec_ref(base);
#ifndef TRUST_IR_LEAN430
    lean_object* world = lean_io_mk_world();
#endif
    lean_object* first = TRUST_IR_ATTACHMENT_INITIALIZER(1 TRUST_IR_INIT_WORLD_ARG);
    lean_object* second = TRUST_IR_ATTACHMENT_INITIALIZER(1 TRUST_IR_INIT_WORLD_ARG);
#if TEST_MODE == 0
    int valid = !lean_io_result_is_error(first) && !lean_io_result_is_error(second);
#else
    int valid = lean_io_result_is_error(first) && lean_io_result_is_error(second);
#endif
    valid = valid && calls == 1 && observed_builtin == 1;
#ifdef TRUST_IR_LEAN430
    valid = valid && observed_world == NULL;
#else
    valid = valid && observed_world == world;
#endif
    lean_dec_ref(first);
    lean_dec_ref(second);
    if (!valid) return 72;
    lean_object* marker = lean_dbg_trace(
        lean_mk_string("INITIALIZER_CONTROL_PASS mode=" STRINGIFY(TEST_MODE) " calls=1"),
        lean_alloc_closure((void*)control_marker, 1, 0));
    lean_dec(marker);
    return 0;
}
