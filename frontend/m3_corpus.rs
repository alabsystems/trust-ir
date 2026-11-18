// M3 corpus: generics + trait static dispatch.
//
// The frontend (M3) reads the GENERIC `thir_body` of these defs and lowers them
// PER concrete instantiation, substituting the generic type params using a
// constructed `Instance` (def_id + GenericArgs) so every `Ty` the pass sees
// is concrete -> trust_ir::Ty.

// M5.7a NESTED-CONSTRUCTOR match patterns (`App(deref!(Lam(_)), _)`, the
// canonical β-redex shape). The nested ctor sits on a `Box<Term>` FIELD;
// current Rust spells this explicit nested dereference with `deref!` under
// `deref_patterns`. Keep the nested pattern rather than splitting it into
// sequential matches: the frontend must still classify the outer App field's
// dereference and inner Lam constructor together. A bare `Term::Lam(_)` cannot
// match a `Box<Term>` field. The pinned compiler lowers the explicit deref
// pattern to THIR `DerefPattern`, which the existing frontend handles.
#![feature(deref_patterns)]

// --- 1. A small generic identity over a primitive / scalar -------------------
// Lower TWO instantiations: id::<u32> and id::<i64>. Each is a distinct concrete
// trust_ir::Function `fn(T) -> T` with `ret x`.
pub fn id<T>(x: T) -> T {
    x
}

// A generic that does a real scalar op (so the two instantiations differ in the
// emitted typed `add` instruction width, not just the signature).
pub fn double<T: std::ops::Add<Output = T> + Copy>(x: T) -> T {
    x + x
}

// --- 1b. A generic CALL CHAIN: `quad` calls `double` (twice, nested) ----------
// This is M4's subject. `quad<T>` is itself generic, and its body CALLS the
// (also generic) `double<T>` — a real cross-function, generic-through-generic
// edge. Monomorphizing `quad<i64>` must recursively resolve+lower `double<i64>`
// as a SEPARATE concrete Function and emit a cross-function `Call` edge to it
// (NOT inline `x + x`). The nesting `double(double(x))` also forces operand
// lowering to recurse into a user-fn Call.
pub fn quad<T: std::ops::Add<Output = T> + Copy>(x: T) -> T {
    double(double(x))
}

// --- 1c. M5.1 control flow: `if`/`else` + multi-param functions ---------------
// `pick` isolates an `if`/`else` join over a bool condition with two i64
// branches, multi-param binding, and VarRef in each branch — no comparison.
pub fn pick(c: bool, a: i64, b: i64) -> i64 {
    if c {
        a
    } else {
        b
    }
}

// `max2` adds a comparison condition (`>=`, a signed integer compare) feeding the
// `if`. The comparison lowers to a trust-ir `icmp Sge` (THIR `Binary { Ge }`).
pub fn max2(a: i64, b: i64) -> i64 {
    if a >= b {
        a
    } else {
        b
    }
}

// `select` proves `if`/join works UNDER monomorphization: a generic
// `fn(bool, T, T) -> T` whose body is an `if`, lowered at T = i64.
pub fn select<T: Copy>(c: bool, a: T, b: T) -> T {
    if c {
        a
    } else {
        b
    }
}

// --- 1d. M5.2 `let`-bindings (multi-statement blocks) -------------------------
// The most pervasive shape in real clean-kernel `tc/` helpers. Both are
// non-generic to isolate the let machinery from monomorphization.
//
// `poly`: sequential `let`s with value reuse. `a = x + x` (= 2x), then
// `b = a + x` (= 3x), tail `b`. Exercises: a block with two `let` stmts before
// the tail, a local FEEDING a later local, and a VarRef resolving to a local.
pub fn poly(x: i64) -> i64 {
    let a = x + x;
    let b = a + x;
    b
}

// `quad_let`: a `let` whose initializer is a CALL, feeding a second call (chain
// through a local). `d = double(x)` (= 2x), tail `double(d)` (= 4x). Proves a
// helper called inside a `let` initializer is discovered for the worklist.
pub fn quad_let(x: i64) -> i64 {
    let d = double(x);
    double(d)
}

// `twice_let`: a `let` UNDER monomorphization — a generic `fn(T)->T` whose body
// binds `d = x + x` and returns it. Lowered at T = i64 it is `double` written
// with an explicit local.
pub fn twice_let<T: std::ops::Add<Output = T> + Copy>(x: T) -> T {
    let d = x + x;
    d
}

// --- 1e. M5.3 `match`-as-VALUE over a scalar (integer) discriminant ----------
// `classify` is a value-producing `match` over an i64 scrutinee with integer
// literal arms and a catch-all `_`: it switches on the scalar VALUE directly
// (not an enum tag Load) and JOINs each arm's result at a block-param. This is
// the structural prerequisite for M5.4 (match over a recursive ADT).
pub fn classify(x: i64) -> i64 {
    match x {
        0 => 100,
        1 => 200,
        7 => 700,
        _ => 999,
    }
}

// `step` exercises arm bodies that CALL a helper plus a BINDING catch-all `n`
// (binding the scrutinee value into a local): `0 => double(x + 1)` and
// `n => double(n)`. Proves a helper called inside a match arm is discovered for
// the worklist and that the scrutinee binds into `locals`.
pub fn step(x: i64) -> i64 {
    match x {
        0 => double(x + 1),
        n => double(n),
    }
}

// `sign` (M5.3 audit FIX #4) exercises NEGATIVE and BOUNDARY integer-literal
// patterns in a scalar match — the previous classify corpus only used the non-
// negative literals 0/1/7, so `eval_pat_const_int` for a NEGATIVE literal (`-1`)
// and the extreme boundary `i64::MIN` was never exercised. A miscompile in the
// signed leaf decode (sign-extension / `to_int`) would silently mis-route. The
// catch-all proves the default arm still fires for an unlisted value.
pub fn sign(x: i64) -> i64 {
    match x {
        -1 => 100,
        0 => 200,
        i64::MIN => 300,
        _ => 999,
    }
}

// --- 1f. M5.4 `match` over a RECURSIVE ADT (value-returning + recursion) ------
// `Level` is the EXISTING M1/M2 recursive-enum shape (Zero/Succ/Max/IMax/Param,
// the clean-kernel `Level`), modeled as the faithful Box-heap tagged struct
// `{ tag: i32 @0, p0: ptr @8, p1: ptr @16 }` (see frontend/src/model.rs, which
// also supplies the heap builder + native oracle reused by the M5.4 differential).
//
// `count_succ` is a VALUE-producing (i64) recursive fold over `Level`: it counts
// the total number of `Succ` nodes anywhere in the tree. It exercises (a) a
// heap-tag `match` lowered through the unified `lower_expr` (tag Load + Switch +
// per-arm payload binding + JOIN at a block-param), (b) a leaf arm (`Zero`,
// `Param`), (c) a single-recursive arm (`Succ`), (d) a binary-recursive arm
// (`Max`/`IMax`, two self-calls summed), and (e) recursion via the worklist
// (the self-call `count_succ(inner)` resolves to this same instance's FuncId).
pub enum Level {
    Zero,
    Succ(Box<Level>),
    Max(Box<Level>, Box<Level>),
    IMax(Box<Level>, Box<Level>),
    Param(u64),
}

pub fn count_succ(l: &Level) -> i64 {
    match l {
        Level::Zero => 0,
        Level::Succ(inner) => 1 + count_succ(inner),
        Level::Max(l1, l2) => count_succ(l1) + count_succ(l2),
        Level::IMax(l1, l2) => count_succ(l1) + count_succ(l2),
        Level::Param(_) => 0,
    }
}

// --- 1g. M5.6 CAPSTONE: REAL clean-kernel `Level::is_zero`/`is_nonzero` -------
// The ACTUAL recursive bool-returning predicate the LowerCx M1/M2 path
// hand-targeted (`Level::is_zero`/`is_nonzero`), now lowered through the UNIFIED
// `MonoCx::lower_expr` — proving MonoCx subsumes the M1/M2 leaf class on genuine
// clean-kernel code. These are written as METHODS: the self-call `a.is_zero()`
// desugars to `Level::is_zero(a)` (an FnDef Call that `resolve_user_call` /
// `Instance::try_resolve` resolves through the worklist, exactly like the free-fn
// `count_succ` self-call). The arms are written to MATCH the native oracle
// (`model::Micro::is_zero`/`is_nonzero`) EXACTLY so the M5.6 differential reuses
// the EXISTING M1/M2 heap builder + oracle:
//   is_zero:    Zero=>true, Succ=>false, Param=>false,
//               Max(a,b)=>a.is_zero() && b.is_zero(), IMax(_,b)=>b.is_zero()
//   is_nonzero: Zero=>false, Param=>false, Succ=>true,
//               Max(a,b)=>a.is_nonzero() || b.is_nonzero(), IMax(_,b)=>b.is_nonzero()
// `is_nonzero` is written as its OWN match (not `!self.is_zero()`) so no `Unary`
// lift is needed and the recursion is self-referential through the worklist. This
// exercises: heap-tag `match` over the recursive ADT (M5.4), `&&`/`||` short-
// circuit (M5.1), bool literals, and worklist recursion on a bool-returning fn.
impl Level {
    pub fn is_zero(&self) -> bool {
        match self {
            Level::Zero => true,
            Level::Succ(_) | Level::Param(_) => false, // Succ always > 0; Params might be 0 at runtime
            Level::Max(l1, l2) => l1.is_zero() && l2.is_zero(),
            Level::IMax(_, l2) => l2.is_zero(), // imax(_, 0) = 0
        }
    }
    pub(crate) fn is_nonzero(&self) -> bool {
        match self {
            Level::Zero | Level::Param(_) => false, // Zero is 0; Params might be 0
            Level::Succ(_) => true,                 // succ(l) > 0 for all l
            Level::Max(l1, l2) => l1.is_nonzero() || l2.is_nonzero(),
            Level::IMax(_, l2) => l2.is_nonzero(), // If l2 > 0, imax reduces to max
        }
    }
}

// --- 1h. Scalar DEREF: `*r` of a `&i64` is a typed Load, NOT a pointer --------
// `deref_add` exercises the scalar-deref path: `r: &i64`, so `*r` must lower to a
// typed `Load(i64, r)` (dereference the pointer, read the i64), THEN add 1 — not
// an identity-peel that returns the pointer typed as i64 (a miscompile the M5
// audit found in the Deref arm). The differential proves it loads + adds.
pub fn deref_add(r: &i64) -> i64 {
    *r + 1
}

// --- 1i. M5.7b INLINE-SCALAR enum payload: a tiny expression evaluator --------
// `Val` is a recursive enum that MIXES a SCALAR leaf payload (`Lit(i64)`) with
// Box children (`Neg`/`Add`). It is the microcosm of a kernel term fold WITH a
// scalar leaf — exactly the shape a real `is_def_eq` needs to compare de Bruijn
// indices (`Expr::Var(i64)`).
//
// Binding semantics (the M5.7b core): matching `&Val`,
//   - `Lit(n)` binds the INLINE i64 by-ref: `n: &i64` = the ADDRESS of the inline
//     value at the slot (a GEP, NO Load); the body's `*n` (the M5.4 scalar-Deref
//     path) then Loads the i64 at the right width;
//   - `Neg(a)` / `Add(a, b)` bind Box CHILDREN: each is a stored pointer
//     (`Load(Ptr, GEP)`, the M5.4 pointer path), passed to the recursive `eval`.
// `eval` combines this with M5.7c unary `-` (`-eval(a)`) and `+` (`eval(a) +
// eval(b)`), all through the SAME unified `MonoCx::lower_expr`.
pub enum Val {
    Lit(i64),
    Neg(Box<Val>),
    Add(Box<Val>, Box<Val>),
}

pub fn eval(v: &Val) -> i64 {
    match v {
        Val::Lit(n) => *n,
        Val::Neg(a) => -eval(a),
        Val::Add(a, b) => eval(a) + eval(b),
    }
}

// --- 1j. M5.7a NESTED-CONSTRUCTOR match patterns (the canonical β-redex shape) -
// `Term` is the lambda-calculus term enum a real clean-kernel `whnf` folds over.
// A β-redex is `App(Lam(..), ..)` — an application whose function is a lambda.
// Detecting it is a NESTED-CONSTRUCTOR pattern: the OUTER `App` with a one-level
// nested `Lam` constructor on its first (Box) field. Until M5.7a this BAILED (the
// fail-loud soundness guard); M5.7a lowers the COMMON one-level case as a decision
// sub-tree — the outer Switch routes `App` to a candidate block that loads the
// first child's inner tag, compares it to `Lam`'s discriminant, and `condbr`s to
// the arm body (match) or the catch-all (mismatch, first-match fallthrough).
//
// NOTE: the field remains `Box<Term>`, so the nested constructor is written
// `deref!(Term::Lam(..))`. This explicit dereference retains the one-level
// nested constructor, including the inner payload binding in the second case;
// it does not replace that case with a flat match or a separate helper call.
pub enum Term {
    Var(i64),
    Lam(Box<Term>),
    App(Box<Term>, Box<Term>),
}

// The CORE M5.7a proof: redex detection via a one-level nested constructor. No
// inner binding — `deref!(Term::Lam(_))` is a nested ctor whose own field is `_`.
pub fn is_beta_redex(t: &Term) -> bool {
    match t {
        Term::App(deref!(Term::Lam(_)), _) => true,
        _ => false,
    }
}

// The BINDING variant (the shape whnf's beta-reduction uses): the nested `Lam`
// constructor BINDS its inner body `b` (a `&Term` = the Lam's Box child pointer),
// and the arm body does a FURTHER nested-MATCH on `b` (`&**b`, the M5.4/M5.7b
// path) to test whether the lambda body is a `Var`. This exercises BOTH the M5.7a
// inner binding (`b` bound against the nested child pointer) AND a normal nested
// match on that bound pointer.
pub fn redex_body_is_var(t: &Term) -> bool {
    match t {
        Term::App(deref!(Term::Lam(b)), _) => match &**b {
            Term::Var(_) => true,
            _ => false,
        },
        _ => false,
    }
}

// --- M5.7e: TUPLE/AGGREGATE enum payload + sub-field destructuring ------------
// `Sym` is a recursive enum whose `Span` variant carries an INLINE AGGREGATE
// payload — a single field that is a 2-tuple `(i64, i64)` — alongside a Box-child
// recursive variant (`Cons`) and a leaf (`Nil`). Until M5.7e an aggregate (tuple/
// struct) payload BAILED loud (the M5.7b/f guard): the tagged-struct model had one
// 8-byte Ptr-or-scalar slot per variant FIELD, with no layout for a SUB-aggregate.
//
// M5.7e reads the REAL offsets from `tcx.layout_of` (M6): the `Span` variant's
// tuple field sits at the variant's field-0 offset, and the tuple's OWN sub-fields
// (`(i64, i64)`) sit at their offsets WITHIN. Binding `(a, b)` from `Span((a, b))`
// GEPs to the tuple's offset, then GEP+Loads each sub-field at its real offset.
// `Cons(t)` is the unchanged M5.4 Box-child pointer path; `Nil` is a leaf. The
// differential drives the THIR-lowered `sym_sum` over real `Sym` heap graphs
// (inline-tuple `Span`, Box `Cons`, leaf `Nil`) vs a native oracle.
//
// NOTE on scope: this is the AGGREGATE-AS-ENUM-PAYLOAD (heap, by-ref via the slot)
// case. Returning/constructing a tuple/struct BY VALUE is DEFERRED (bail loud) —
// Rust passes small aggregates in registers per AAPCS64 and the frontend has no
// struct-by-value ABI, so a by-ref model would mismatch the C ABI round-trip.
pub enum Sym {
    Nil,
    Span((i64, i64)),
    Cons(Box<Sym>),
}

// `sym_sum` folds a `Sym` tree to an i64: `Span((a, b))` binds the tuple's two
// sub-fields and sums them; `Cons(t)` recurses on the Box child; `Nil` is 0. The
// `Span` arm is the M5.7e CORE — destructuring a by-ref aggregate payload's
// sub-fields at their real layout offsets.
pub fn sym_sum(s: &Sym) -> i64 {
    match s {
        Sym::Nil => 0,
        // `a`/`b` bind the tuple's two sub-fields by-ref (`&i64`, the addresses of
        // the inline values); `*a`/`*b` are the M5.4/M5.7b scalar-Deref Loads that
        // read each i64 at its real offset before the add. (Explicit `*` mirrors the
        // M5.7b `eval`'s `Lit(n) => *n` idiom — it forces the typed Load rather than
        // relying on the `&i64: Add` reference-operator impl, which the frontend does
        // not model.)
        Sym::Span((a, b)) => *a + *b,
        Sym::Cons(t) => sym_sum(t),
    }
}

// --- FIX 5: NARROW / DISTINCT-WIDTH aggregate sub-fields ----------------------
// The M5.7e `Sym::Span((i64, i64))` exercises an inline aggregate, but BOTH
// sub-fields are i64 — so the heap builder's Store width and the lowered reader's
// Load width are both I64, and a wrong width/offset would be MASKED (writing and
// reading the same wrong width still round-trips). `Pair::Cell((i32, i32))` closes
// that with a NARROW width distinct from I64: each sub-field is Loaded/Stored at
// I32 (not I64), at the i32 stride (offsets 0 and 4 within the tuple, NOT the
// 8-stride). An I64-width Load of the first i32 would also pull in the second
// i32's bytes; a wrong offset (8 instead of 4) would miss it — either mis-sums.
// (The truly-narrow i8 / mixed (i8,i64) form would need an `as`/`From` widening
// cast to combine with an i64, which the frontend does not lower — see the report;
// the i32+i32 form exercises the same narrow-width Load/Store + offset discipline
// without a cast, since i32 + i32 -> i32 needs no widening.)
//
// rustc lays `(i32, i32)` out as size 8, align 4: sub-offsets 0 and 4. `Pair` is
// `Direct`-tagged, so `Cell`'s tuple field sits past the tag and each i32 is read
// at its real I32 width + offset (recovered from `layout_of`, not assumed).
pub enum Pair {
    End,
    Cell((i32, i32)),
    Next(Box<Pair>),
}

// `pair_sum` folds a `Pair` tree to an i32: `Cell((a, b))` binds the two NARROW i32
// sub-fields and sums them at I32 width (wrapping); `Next(t)` recurses on the Box
// child; `End` is 0. The `Cell` arm is the distinct-(narrow-)width CORE: `*a`/`*b`
// each Load an i32 at the tuple's real sub-offset.
pub fn pair_sum(p: &Pair) -> i32 {
    match p {
        Pair::End => 0,
        // `a: &i32`, `b: &i32`. `*a` Loads an i32 at sub-offset 0, `*b` an i32 at
        // sub-offset 4; the `+` lowers to the trust-ir I32 `add` (which WRAPS, the
        // semantics the native oracle mirrors with `wrapping_add`). The corpus is
        // never executed natively (it is compiled THROUGH the frontend), so the
        // debug-overflow panic on `+` never fires; the frontend lowers `+` to a
        // wrapping I32 add. A wrong narrow Load width or sub-field offset mis-sums.
        Pair::Cell((a, b)) => *a + *b,
        Pair::Next(t) => pair_sum(t),
    }
}

// --- 2. Trait with one method + one impl, called on a concrete type ----------
pub trait Predicate {
    fn pred(&self) -> bool;
}

pub struct Yes;
pub struct No;

impl Predicate for Yes {
    fn pred(&self) -> bool {
        true
    }
}

impl Predicate for No {
    fn pred(&self) -> bool {
        false
    }
}

// A monomorphic call site: `Yes.pred()` resolves (via Instance::try_resolve) to
// the `<Yes as Predicate>::pred` impl method -> a DIRECT Inst::Call to that
// monomorphized callee (NOT a generic/virtual dispatch).
pub fn call_yes() -> bool {
    let y = Yes;
    y.pred()
}

// A SECOND call site on a different concrete Self type: proves `try_resolve`
// genuinely dispatches per-Self (Yes -> true-impl, No -> false-impl), not a
// hardcoded single resolution.
pub fn call_no() -> bool {
    let n = No;
    n.pred()
}

// --- 3. A trait whose impl method body is NON-CONSTANT (generality proof) ----
// The `Predicate` impls above return a bool LITERAL, so a constant-only special
// case could lower them. `Score` proves the trait-dispatch path lowers the
// resolved impl method's BODY through the UNIFIED `lower_expr` (an i64 arithmetic
// expression — `1 + 1`, `0 - 7` — not a literal) and DERIVES the callee sig
// (`fn(Ptr) -> i64`, not a hardcoded `(Ptr) -> Bool`).
pub trait Score {
    fn score(&self) -> i64;
}

pub struct Two;
pub struct Neg;

impl Score for Two {
    fn score(&self) -> i64 {
        1 + 1
    }
}

impl Score for Neg {
    fn score(&self) -> i64 {
        0 - 7
    }
}

// `Two.score()` resolves to `<Two as Score>::score` -> a DIRECT Call whose callee
// body is `add(1, 1)` lowered via lower_expr; result 2.
pub fn call_two() -> i64 {
    Two.score()
}

// `Neg.score()` resolves to `<Neg as Score>::score`; callee body `sub(0, 7)`;
// result -7. A SECOND Self proves per-Self resolution for the i64 trait too.
pub fn call_neg() -> i64 {
    Neg.score()
}

// --- M5.7c: unary operators + the rest of the integer binops ------------------
// These exercise the additive M5.7c lowering (`ExprKind::Unary` + `lower_binop`
// Div/Rem/BitAnd/BitOr/BitXor/Shl/Shr) through the SAME unified `MonoCx::lower_expr`.
// Each is a leaf `fn` (no cross-fn Call) over i64 / bool, driven by the M5.7c
// differential against a GENUINE native Rust oracle (computed the same way M4's
// `quad_oracle` is — not a hand literal).

// Unary `-` on a signed integer -> trust-ir `UnOp::Neg` (0 - x, wrapping).
pub fn negate(x: i64) -> i64 {
    -x
}

// Bool `!` -> a `Select(b, false, true)` (the trust-ir interpreter models bool
// as a distinct value kind, so a native bitwise Not / icmp typed Bool would
// trap; Select over a bool is the correct shape).
pub fn bnot(b: bool) -> bool {
    !b
}

// Integer `!` -> trust-ir `UnOp::Not` (bitwise complement at i64 width).
pub fn inot(x: i64) -> i64 {
    !x
}

// Bit-logic: BitAnd, BitXor, BitOr in one expression.
pub fn bitops(a: i64, b: i64) -> i64 {
    (a & b) | (a ^ b)
}

// Signed division + remainder. The differential drives this ONLY with a
// non-zero divisor `b` (the interpreter traps on a zero divisor — that is its
// defined UB, which we do not add to).
pub fn divrem(a: i64, b: i64) -> i64 {
    (a / b) + (a % b)
}

// Left then signed-right shift. The differential drives this ONLY with a shift
// amount `0 <= n < 64` (the interpreter traps on an out-of-range shift).
// `a << n >> n` round-trips `a` only when it fits in `64 - n` significant bits;
// the oracle computes the SAME wrapping shifts so any value is fine to test.
pub fn shifts(a: i64, n: i64) -> i64 {
    (a << n) >> n
}

// --- M5.7d: MULTI-type-param generic monomorphization -------------------------
// Until now the frontend only monomorphized a SINGLE type param (`id<T>`,
// `double<T>`). These have TWO type params, monomorphized POSITIONALLY at
// distinct concrete tuples to prove per-instantiation IR differs by type/width.
// Both are leaf bodies lowered through the SAME unified `MonoCx::lower_expr`.

// `fst<A, B>(a: A, b: B) -> A { a }` — a two-type-param generic whose RETURN type
// is the FIRST param. Instantiated `fst<i64,u32>` returns i64 (64-bit) and
// `fst<u32,i64>` returns u32 (32-bit): swapping the type tuple flips the return
// width, so the two instantiations are NOT the same IR. `_b` is bound but unused.
pub fn fst<A: Copy, B: Copy>(a: A, _b: B) -> A {
    a
}

// `combine<A, B>(a: A, b: A, _w: B) -> A { a + b }` — the FIRST type param `A`
// carries an `Add` bound (the real arithmetic happens at width A); the SECOND
// type param `B` is an unused "weight" type that only proves a second,
// independent type param is bound and substituted. `combine<u32>(_)` wraps at 32
// bits (`0x8000_0000 + 0x8000_0000 == 0` at U32) while `combine<i64>(_)` does not
// — a width-discriminating witness that the per-instantiation width is honored.
pub fn combine<A: Copy + core::ops::Add<Output = A>, B: Copy>(a: A, b: A, _w: B) -> A {
    a + b
}

// A CONST-generic fn — the M5.7d entry must REJECT this loudly (binding a const
// param needs a const value, which `args_for_type_params` does not supply). Only
// exercised by the env-gated `M5H_PROBE_BAILS` diagnostic in the driver; never on
// the default path (so the normal --m3 output is unchanged).
pub fn with_const<const N: usize>(x: i64) -> i64 {
    x + (N as i64)
}

// --- M5.7f: ENUM-VARIANT CONSTRUCTION (the DUAL of lower_match_adt) ------------
// Until M5.7f every enum-variant CONSTRUCTION bailed (the audit's fail-loud
// guard in `lower_zst_adt`): the frontend could only READ a tagged-struct heap
// value (a `match`), never BUILD one. M5.7f adds the construction path — the key
// remaining capability for a real `whnf` (which BUILDS the reduced term):
//   `p = HeapAlloc(<the enum's tagged struct>)`, `Store(i32 discr, GEP(p,@0))`,
//   then per field i: lower the field VALUE and `Store` it at `GEP(p, @8+8i)`
//   (a Box child stores the inner POINTER; an inline scalar stores the VALUE).
//   The constructor expression's value is `p` (a Ptr). `Box::new(e)` peels to its
//   inner argument (the inner construction alloc IS the Box pointer).
//
// These are CONSTRUCT-THEN-FOLD functions: they BUILD a closed `Level`/`Val`
// term with the new construction path, then FOLD it through the EXISTING match
// path (`count_succ`/`eval`) to an i64 result that the differential checks
// against a GENUINE native oracle — so a wrong construction (wrong tag, wrong
// slot, missing Store) shows up as a wrong fold.

// `one()` builds `Succ(Zero)` — a one-level Box nesting (the inner `Zero` alloc
// IS the Box pointer stored in `Succ`'s slot 0).
pub fn one() -> Level {
    Level::Succ(Box::new(Level::Zero))
}

// `one_depth()` builds `Succ(Zero)` and folds it: count_succ -> 1.
pub fn one_depth() -> i64 {
    count_succ(&one())
}

// `two_depth()` builds `Succ(Succ(Zero))` INLINE (two nested `Box::new`) and
// folds it: count_succ -> 2. Proves multi-level recursive construction.
pub fn two_depth() -> i64 {
    count_succ(&Level::Succ(Box::new(Level::Succ(Box::new(Level::Zero)))))
}

// `lit(n)` builds `Val::Lit(n)` — a SCALAR-payload variant: the i64 `n` is
// stored INLINE at slot 0 (no Box), the dual of M5.7b's inline-scalar read.
pub fn lit(n: i64) -> Val {
    Val::Lit(n)
}

// `lit_eval(n)` builds `Lit(n)` and evals it: eval -> n.
pub fn lit_eval(n: i64) -> i64 {
    eval(&lit(n))
}

// `neg_lit(n)` builds `Neg(Lit(n))` — a Box child (`Neg`'s slot 0 holds the
// `Lit(n)` pointer) wrapping a scalar leaf — and evals it: eval -> -n. Combines
// inline-scalar construction with Box-child construction in one term.
pub fn neg_lit(n: i64) -> i64 {
    eval(&Val::Neg(Box::new(Val::Lit(n))))
}

// --- FIX 2: NICHE UNTAGGED-VARIANT CONSTRUCTION coverage ----------------------
// `lower_enum_variant_construction`'s `is_niche_untagged` branch stores NO tag —
// the constructed variant's own payload (a real Box pointer) provides the
// discriminant, and it must read back as the Switch DEFAULT. The M5.7f Level/Val
// construct-then-fold fns above only ever construct DIRECT-tagged variants (every
// variant stores an explicit tag), so the niche untagged-construction path was
// UNTESTED. `NBox` closes that: a NICHE-encoded enum whose UNTAGGED variant holds
// a `Box` payload.
//
// rustc lays `NBox` out (verified via `#[rustc_layout(debug)]`) as:
//   tag_encoding = Niche { untagged_variant: 1 (=Cons), niche_variants: 0..=0,
//   niche_start: 0 } — i.e. `Nil` (variant 0) is the niche-encoded variant (its
//   niche value is the null pointer, 0), and `Cons(Box<NBox>)` (variant 1) is the
//   UNTAGGED variant: it stores its real Box pointer and is the Switch DEFAULT.
// So CONSTRUCTING `Cons(Box::new(..))` exercises the no-tag-store untagged branch,
// and folding it back through `nbox_depth` (whose `Cons` arm is the Switch
// default) confirms the constructed untagged value reads back as `Cons`.
pub enum NBox {
    Nil,
    Cons(Box<NBox>),
}

// Read-back fold: counts the `Cons` nesting depth. `Cons` is the niche untagged
// variant = the Switch DEFAULT; `Nil` is the niche-encoded (null) case.
pub fn nbox_depth(x: &NBox) -> i64 {
    match x {
        NBox::Nil => 0,
        NBox::Cons(inner) => 1 + nbox_depth(inner),
    }
}

// `nbox_nil_depth()` builds the niche-ENCODED `Nil` and folds it -> 0.
pub fn nbox_nil_depth() -> i64 {
    nbox_depth(&NBox::Nil)
}

// `nbox_one_depth()` CONSTRUCTS the niche UNTAGGED variant `Cons(Box::new(Nil))`
// (one no-tag-store untagged alloc wrapping the niche-encoded `Nil`) and folds it
// -> 1. If the untagged construction wrongly stored a synthetic tag (or the wrong
// pointer), the read-back fold would mis-route and the depth would be wrong.
pub fn nbox_one_depth() -> i64 {
    nbox_depth(&NBox::Cons(Box::new(NBox::Nil)))
}

// `nbox_two_depth()` CONSTRUCTS two nested untagged `Cons` (each a no-tag-store
// untagged alloc) over `Nil` and folds it -> 2. Proves multi-level niche untagged
// construction.
pub fn nbox_two_depth() -> i64 {
    nbox_depth(&NBox::Cons(Box::new(NBox::Cons(Box::new(NBox::Nil)))))
}

fn main() {}
