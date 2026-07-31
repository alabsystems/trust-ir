/* ASan/LSan harness: exercises the runtime's heap paths (Box::new, Box::clone,
 * HashMap memo clone+free, Vec::push realloc) via trust-cg fns and frees every
 * result, so ASan can flag any leak / double-free / use-after-free / OOB. */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

extern void Level__zero(void*);
extern void Level__param(void*, unsigned);
extern void Level__succ(void*, const void*);
extern void Level__max(void*, const void*, const void*);
extern void Level__imax(void*, const void*, const void*);
extern void Level__add_offset(void*, const void*, unsigned);
extern void Level__normalize(void*, const void*);
extern unsigned char Level__is_geq(const void*, const void*);
extern void Level__collect_params(const void*, void*);
typedef struct { uint32_t* data; size_t len; size_t cap; } NameVec;

typedef struct { uint32_t data[6]; } L; /* 24-byte Level buffer */

/* recursively free a Level's boxed children (mirrors ownership) */
static void lfree_children(void* lp) {
    int32_t tag = *(int32_t*)lp;
    void* c1 = *(void**)((char*)lp + 8);
    void* c2 = *(void**)((char*)lp + 16);
    if (tag == 1) { lfree_children(c1); free(c1); }
    else if (tag == 2 || tag == 3) { lfree_children(c1); free(c1); lfree_children(c2); free(c2); }
}
static void mk_zero(void* o){ Level__zero(o); }
static void mk_param(void* o, unsigned n){ Level__param(o, n); }
/* build Succ^k(base) in o, consuming base (base bytes copied) */
static void mk_succ(void* o, const void* in){ Level__succ(o, in); }

int main(void){
    for (int iter = 0; iter < 200; iter++) {
        L a, b, r;
        /* max(Param(i), Succ(Param(j))) -> exercises Box::new */
        L pj; mk_param(&pj, iter%7);
        mk_succ(&a, &pj);                 /* a = Succ(Param) ; consumes pj bytes */
        mk_param(&b, (iter+3)%7);
        Level__max(&r, &a, &b);           /* consumes a,b */
        lfree_children(&r);               /* free result subtree (a,b heap now owned by r) */

        /* add_offset(Param, k): Box::new + clone + Range */
        L p2, ao; mk_param(&p2, iter%5);
        Level__add_offset(&ao, &p2, (unsigned)(iter%6));
        lfree_children(&ao);

        /* is_geq on Max trees: HashMap memo -> clones keys then frees them */
        L m1, m2, x, y, z, w;
        mk_param(&x, 1); mk_param(&y, 2); Level__max(&m1, &x, &y);
        mk_param(&z, 1); mk_param(&w, 3); Level__max(&m2, &z, &w);
        volatile unsigned char g = Level__is_geq(&m1, &m2);
        (void)g;
        lfree_children(&m1); lfree_children(&m2);

        /* normalize(IMax(Param,Param)) */
        L i1,i2,im,nm; mk_param(&i1, iter%4); mk_param(&i2,(iter+1)%4);
        Level__imax(&im, &i1, &i2);
        Level__normalize(&nm, &im);
        lfree_children(&im); lfree_children(&nm);

        /* collect_params(Max(Param, Max(Param,Param))): Vec::push realloc path */
        L cp1,cp2,cp3,inner,outer;
        mk_param(&cp1, 1); mk_param(&cp2, 2); Level__max(&inner, &cp1, &cp2);
        mk_param(&cp3, 3); Level__max(&outer, &cp3, &inner);
        NameVec v = { NULL, 0, 0 };
        Level__collect_params(&outer, &v);
        if (v.data) free(v.data);
        lfree_children(&outer);
    }
    printf("asan harness ok\n");
    return 0;
}
