/*
 * Minimal runtime for the first-party clean-kernel `Level` slice compiled by
 * trust-cg from the trust-ir closure modules.
 *
 * The frontend's `--mir-emit-closure` lowers every crate-local fn (the 34
 * first-party Level fns + derived Clone/PartialEq/Hash for Level/Name +
 * closure combinators like unwrap_or_else) INTO the module. What it leaves as
 * external leaves are the monomorphized *std generics* the corpus imports by
 * mangled name. This file provides exactly those leaves, defined with their
 * exact Mach-O symbol names via verbatim `__asm__("...")` labels (a leading
 * `__` = one v0 `_R...` underscore + one Mach-O underscore). In-module derived
 * impls are `__Level_as_std__...` (double); trust-cg method names are single.
 *
 * Level layout (verified against a stage1-rustc layout probe and the emitted
 * IR): size 24, align 8; i32 tag @0 (Zero=0 Succ=1 Max=2 IMax=3 Param=4);
 * Param's Name(u32) @4; Box child pointers @8 and @16.
 * Option<Level> reuses the 24-byte layout with tag=5 as the None niche.
 */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#define LVL_SIZE 24

/* ---- in-module symbols provided by the trust-cg closure object ---------- */
extern unsigned char Level_derived_eq(const void *a, const void *b)
    __asm__("__Level_as_std__cmp__PartialEq___eq");
extern void Level_derived_clone(void *out, const void *self)
    __asm__("__Level_as_std__clone__Clone___clone");
extern void Level_succ(void *out, void *in_level)
    __asm__("_Level__succ");

/* ---- recursive drop of a Level's boxed children (memo-key cleanup) ------- */
static void level_drop_children(const void *lp);
static void box_free(void *boxp) { /* boxp: heap Level */
    level_drop_children(boxp);
    free(boxp);
}
static void level_drop_children(const void *lp) {
    int32_t tag = *(const int32_t *)lp;
    void *c1 = *(void *const *)((const char *)lp + 8);
    void *c2 = *(void *const *)((const char *)lp + 16);
    if (tag == 1) { box_free(c1); }                        /* Succ */
    else if (tag == 2 || tag == 3) { box_free(c1); box_free(c2); } /* Max/IMax */
    /* Zero(0), Param(4): no owned heap */
}

/* ---- alloc::boxed: Box::<Level>::new(out_slot, src_level) --------------- */
void tir_box_new(void **out, const void *src)
    __asm__("__RNvMNtCs7Ghp21B2VXc_5alloc5boxedINtB2_3BoxNtCskQsKCQTGqGW_17clean_level_slice5LevelE3newBG_");
void tir_box_new(void **out, const void *src) {
    void *p = malloc(LVL_SIZE);
    memcpy(p, src, LVL_SIZE);
    *out = p;
}

/* ---- alloc::boxed: <Box<Level> as Clone>::clone(out_slot, &box) --------- */
void tir_box_clone(void **out, void *const *self)
    __asm__("__RNvXsd_NtCs7Ghp21B2VXc_5alloc5boxedINtB5_3BoxNtCskQsKCQTGqGW_17clean_level_slice5LevelENtNtCs1FFDhjBqhU0_4core5clone5Clone5cloneBJ_");
void tir_box_clone(void **out, void *const *self) {
    const void *src = *self;             /* the boxed Level */
    void *dst = malloc(LVL_SIZE);
    Level_derived_clone(dst, src);       /* deep clone via in-module Level::clone */
    *out = dst;
}

/* ---- core::cmp::impls: <&Name as PartialEq>::eq(&&Name, &&Name) --------- */
unsigned char tir_ref_name_eq(uint32_t **a, uint32_t **b)
    __asm__("__RNvXs7_NtNtCs1FFDhjBqhU0_4core3cmp5implsRNtCskQsKCQTGqGW_17clean_level_slice4NameNtB7_9PartialEq2eqBF_");
unsigned char tir_ref_name_eq(uint32_t **a, uint32_t **b) {
    return (**a == **b) ? 1 : 0;
}

/* ---- core::cmp::impls: <&Level as PartialEq>::eq(&&Level, &&Level) ------ */
unsigned char tir_ref_level_eq(const void **a, const void **b)
    __asm__("__RNvXs7_NtNtCs1FFDhjBqhU0_4core3cmp5implsRNtCskQsKCQTGqGW_17clean_level_slice5LevelNtB7_9PartialEq2eqBF_");
unsigned char tir_ref_level_eq(const void **a, const void **b) {
    return Level_derived_eq(*a, *b) & 1u;
}

/* ---- core::cmp::impls: <&Box<Level> as PartialEq>::eq(&&Box, &&Box) ----- */
unsigned char tir_ref_box_eq(const void ***a, const void ***b)
    __asm__("__RNvXs7_NtNtCs1FFDhjBqhU0_4core3cmp5implsRINtNtCs7Ghp21B2VXc_5alloc5boxed3BoxNtCskQsKCQTGqGW_17clean_level_slice5LevelENtB7_9PartialEq2eqB1e_");
unsigned char tir_ref_box_eq(const void ***a, const void ***b) {
    return Level_derived_eq(**a, **b) & 1u; /* compare the two boxed Levels */
}

/* ---- core::option: Option::<Level>::map::<Level::succ>(out, self) ------- */
void tir_opt_map_succ(void *out, void *self)
    __asm__("__RINvMNtCs1FFDhjBqhU0_4core6optionINtB3_6OptionNtCskQsKCQTGqGW_17clean_level_slice5LevelE3mapBI_NvMBK_BI_4succEBK_");
void tir_opt_map_succ(void *out, void *self) {
    if (*(int32_t *)self == 5) { *(int32_t *)out = 5; }   /* None -> None */
    else { Level_succ(out, self); }                        /* Some(x) -> Some(succ x) */
}

/* ---- core::option: Option::<Level>::is_none(&self) --------------------- */
unsigned char tir_opt_is_none(const void *self)
    __asm__("__RNvMNtCs1FFDhjBqhU0_4core6optionINtB2_6OptionNtCskQsKCQTGqGW_17clean_level_slice5LevelE7is_noneBJ_");
unsigned char tir_opt_is_none(const void *self) {
    return (*(const int32_t *)self == 5) ? 1 : 0;
}

/* ---- core::num: <u32>::saturating_add(a, b) --------------------------- */
uint32_t tir_sat_add(uint32_t a, uint32_t b)
    __asm__("__RNvMs6_NtCs1FFDhjBqhU0_4core3numm14saturating_add");
uint32_t tir_sat_add(uint32_t a, uint32_t b) {
    uint64_t s = (uint64_t)a + (uint64_t)b;
    return s > 0xFFFFFFFFu ? 0xFFFFFFFFu : (uint32_t)s;
}

/* ---- core::iter: <Range<u32> as IntoIterator>::into_iter(out, self) ---- */
void tir_range_into_iter(void *out, const void *self)
    __asm__("__RNvXNtNtNtCs1FFDhjBqhU0_4core4iter6traits7collectINtNtNtB8_3ops5range5RangemENtB2_12IntoIterator9into_iterCskQsKCQTGqGW_17clean_level_slice");
void tir_range_into_iter(void *out, const void *self) {
    memcpy(out, self, 8);                 /* Range<u32> is the identity iterator */
}

/* ---- core::iter: <Range<u32> as Iterator>::next(out, self) ------------- */
/* Range{start@0,end@4} : &mut ; out = Option<u32>{tag i32@0, val i32@4}, None=0 Some=1 */
void tir_range_next(void *out, void *self)
    __asm__("__RNvXs4_NtNtCs1FFDhjBqhU0_4core4iter5rangeINtNtNtB9_3ops5range5RangemENtNtNtB7_6traits8iterator8Iterator4nextCskQsKCQTGqGW_17clean_level_slice");
void tir_range_next(void *out, void *self) {
    uint32_t *r = (uint32_t *)self;
    int32_t *o = (int32_t *)out;
    if (r[0] < r[1]) { o[1] = (int32_t)r[0]; r[0] += 1; o[0] = 1; }
    else { o[0] = 0; }
}

/* ---- std::collections HashMap<(Level,Level),bool> memo (48 bytes) ------ *
 * Correctness-preserving stub: the map is only a memo cache. get() always
 * misses (returns the null-pointer None), insert() drops the moved key (so no
 * leak) and reports no previous value. is_geq_core_cached therefore always
 * recomputes, computing the identical boolean result. new() zeroes the slot;
 * drop_in_place() is a no-op (the map holds nothing). */
void tir_hm_new(void *out)
    __asm__("__RNvMNtNtNtCs5QkB10dUsHY_3std11collections4hash3mapINtB2_7HashMapTNtCskQsKCQTGqGW_17clean_level_slice5LevelB11_EbE3newB13_");
void tir_hm_new(void *out) { memset(out, 0, 48); }

void tir_hm_get(void **out, const void *self, const void *key)
    __asm__("__RINvMs2_NtNtNtCs5QkB10dUsHY_3std11collections4hash3mapINtB6_7HashMapTNtCskQsKCQTGqGW_17clean_level_slice5LevelB15_EbE3getB14_EB17_");
void tir_hm_get(void **out, const void *self, const void *key) {
    (void)self; (void)key;
    *out = 0;                             /* Option<&bool> == None (miss) */
}

void tir_hm_insert(void *out, void *self, void *key, unsigned char val)
    __asm__("__RNvMs2_NtNtNtCs5QkB10dUsHY_3std11collections4hash3mapINtB5_7HashMapTNtCskQsKCQTGqGW_17clean_level_slice5LevelB14_EbE6insertB16_");
void tir_hm_insert(void *out, void *self, void *key, unsigned char val) {
    (void)self; (void)val;
    level_drop_children(key);                       /* key = (Level, Level), 48B */
    level_drop_children((const char *)key + 24);
    *(int8_t *)out = 2;                              /* Option<bool> == None (discarded) */
}

void tir_hm_drop(void *self)
    __asm__("__RINvNtCs1FFDhjBqhU0_4core3ptr13drop_in_placeINtNtNtNtCs5QkB10dUsHY_3std11collections4hash3map7HashMapTNtCskQsKCQTGqGW_17clean_level_slice5LevelB1C_EbEEB1E_");
void tir_hm_drop(void *self) { (void)self; }

/* ---- alloc::vec: Vec::<Name>::push(&mut self, name) -------------------- *
 * The corpus's collect_params only ever calls Vec::push and never inspects the
 * Vec representation, so the runtime owns the layout. The driver builds the
 * same struct, passes &vec, and reads data[0..len] afterwards. */
typedef struct { uint32_t *data; size_t len; size_t cap; } NameVec;
void tir_vec_name_push(NameVec *v, uint32_t name)
    __asm__("__RNvMsF_NtCs7Ghp21B2VXc_5alloc3vecINtB5_3VecNtCskQsKCQTGqGW_17clean_level_slice4NameE4pushBH_");
void tir_vec_name_push(NameVec *v, uint32_t name) {
    if (v->len == v->cap) {
        size_t nc = v->cap ? v->cap * 2 : 4;
        v->data = (uint32_t *)realloc(v->data, nc * sizeof(uint32_t));
        v->cap = nc;
    }
    v->data[v->len++] = name;
}
