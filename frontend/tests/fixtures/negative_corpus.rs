// NEGATIVE corpus — PRESERVED fail-loud regression for the frontend's soundness
// guards.
//
// Each `pub fn` below is an UNSOUND lowering shape the frontend MUST refuse to
// lower (it must print a `LOWERING FAILED: ...` loud bail), NOT silently
// miscompile. Two HIGH silent-miscompiles of the "bare-name trait recognizer"
// class slipped past earlier audits (a user method named `deref` mistaken for a
// pointer dereference; a `+`/`-`/`*` method-name confusion); this file locks the
// guards in so they can never silently regress. `tests/negative_lowering.rs`
// spawns the real `trust_ir_frontend` driver on this file once per fn
// (`--target-fn <name>`) and asserts each one bails loudly.
//
// Every fn is `fn(&self/...) -> bool` whose body's tail is a `match` over an enum
// (the default `--target-fn` driver path = `lower_predicate_to_builder`, which
// only admits a bool-returning enum-match predicate). Each fn is REACHABLE by
// `--target-fn <name>`. The enums are small and LOCAL to this fixture.
//
// DO NOT "fix" any of these by making them lower — that would defeat the
// regression. If a guard is intentionally relaxed in the future, update BOTH the
// guard AND the corresponding assertion here, deliberately.

#![feature(box_patterns)]
#![allow(dead_code, unused_variables)]

// ---- Local enums used by the fixtures ---------------------------------------

// A pointer-payload recursive enum (every payload slot is a real `Box<Self>`),
// the shape the tagged-struct model supports for the OUTER variant.
pub enum Tree {
    Leaf,
    Node(Box<Tree>, Box<Tree>),
}

// An enum carrying an INLINE AGGREGATE (tuple) payload. M5.7e now LOWERS the
// ONE-LEVEL aggregate-destructure (`Span((a, b))`, binding the tuple's two scalar
// sub-fields at their real `layout_of` offsets). The still-unsupported shapes that
// REPLACE the old one-level cases here are:
//   * `Deep(((i64,i64), i64))` — a NESTED aggregate (an aggregate-in-aggregate):
//     destructuring `Deep(((a, b), c))` needs >1 level of sub-field walking, which
//     M5.7e explicitly bails on (only one level is in scope);
//   * binding a WHOLE aggregate by-ref (`Span(p)`, `p: &(i64, i64)`) — still has no
//     8-byte Ptr-or-scalar slot in the tagged-struct model;
//   * CONSTRUCTING an aggregate-payload variant (`Sym::Span((1, 2))`) — the
//     construction side is DEFERRED (M5.7e covers READ/destructure only).
pub enum Sym {
    Nil,
    Span((i64, i64)),
    Deep(((i64, i64), i64)),
}

// M6: the OLD i32-tag guard (a hardcoded I32 tag rejecting an out-of-i32
// discriminant) is RETIRED — the tag width is now FAITHFUL (`layout_of`), so a
// `repr(i64)` enum with a 2^32 discriminant lowers correctly at an i64 tag. The
// guard that remains is the tag-WIDTH cap: trust-ir Loads are i8/i16/i32/i64, so a
// `repr(i128)` enum has a 16-byte discriminant with NO trust-ir Load width — it
// must STILL bail loud (refusing to mis-read a 16-byte tag).
#[repr(i128)]
pub enum Wide {
    Small = 0,
    Huge = 0x1_0000_0000_0000_0001, // forces a 16-byte (i128-width) tag
}

// (Flag removed: constructing a no-payload enum-variant value now LOWERS under
// M5.7f. The construction guard that remains meaningful is the inline-AGGREGATE
// payload construction — `Sym::Span((i64,i64))` below — whose tuple field has no
// tagged-struct slot layout, so its CONSTRUCTION still bails loud, exactly as the
// SYMMETRIC binding side does in `neg_scalar_payload`.)

// A struct with a USER INHERENT method literally named `deref` — NOT the
// `Deref` trait. Misclassifying it as a pointer dereference would silently DROP
// the call (peel to the receiver): the is_deref_call (trait-identity, not bare-
// name) guard. The method RETURNS an enum so it can sit in a match-scrutinee
// PLACE position, exactly where `lower_place` would (wrongly) peel a deref.
pub struct Wrapper {
    pub inner: Tree,
}
impl Wrapper {
    // A plain inherent method that merely happens to be named `deref`,
    // returning a borrow of its field (so it sits in a match-scrutinee place).
    pub fn deref(&self) -> &Tree {
        &self.inner
    }
}

// ---- The fail-loud fixtures (one per guard) ---------------------------------

// GUARD 1 — is_deref_call (bare-name trait recognizer). `w.deref()` is a USER
// inherent method, NOT a `Deref` impl. It sits in the MATCH-SCRUTINEE place — the
// exact spot `lower_place` peels a recognized `Deref::deref` call to its
// receiver. A bare-NAME recognizer would (wrongly) peel `w.deref()` to `w` and
// run the match on the un-deref'd receiver (a silent miscompile); the trait-
// identity guard refuses, so `lower_place` cannot model the Call scrutinee and
// bails LOUDLY instead of silently dropping the call. Reachable via
// `--target-fn neg_user_deref`.
pub fn neg_user_deref(w: &Wrapper) -> bool {
    match w.deref() {
        Tree::Leaf => true,
        Tree::Node(_, _) => false,
    }
}

// GUARD 2 — classify_arm_subpatterns (DEEPER-than-one-level nested constructor).
// M5.7a now LOWERS the COMMON one-level nested ctor (`Node(box Leaf, _)`), but a
// TWO-LEVEL nest — `Node(box Node(box Leaf, _), _)`, the nested `Node` ctor itself
// carrying a nested `Leaf` ctor (its own fields NON-trivial) — is `Unsupported`:
// the single inner tag-check cannot route a second level of nesting, and routing
// the whole outer variant would DROP the deeper constraint. So it must STILL bail
// loud (deeper nesting / a full decision tree is future work). The catch-all `_`
// is present (so the bail is specifically the depth guard, not the
// missing-catch-all guard). Reachable via `--target-fn neg_nested_ctor`.
pub fn neg_nested_ctor(t: &Tree) -> bool {
    match t {
        Tree::Node(box Tree::Node(box Tree::Leaf, _), _) => true,
        _ => false,
    }
}

// GUARD 3 — enum-variant CONSTRUCTION with an inline-AGGREGATE payload. M5.7f LOWERS
// enum-variant construction (no-payload / Box-child / inline-SCALAR variants), and
// M5.7e LOWERS aggregate-payload READING / destructuring (`Span((a, b))`) — but
// CONSTRUCTING an aggregate-payload variant is STILL deferred (M5.7e covers the read
// side only; there is no aggregate-field Store). `let z = Sym::Span((1, 2));`
// constructs a variant whose single field is a 2-tuple `(i64, i64)`, which has no
// tagged-struct slot layout (each slot is one 8-byte Ptr-or-scalar).
// `lower_enum_variant_construction` enters the construction path (HeapAlloc + tag
// Store) but bails LOUD on the aggregate field — the still-unsupported
// construction-side aggregate case. The match itself (over the SAME enum) lowers
// fine; the bail is specifically the aggregate-CONSTRUCTION guard. Reachable via
// `--target-fn neg_construct_variant` (name kept stable for the regression harness).
pub fn neg_construct_variant(s: &Sym) -> bool {
    let z = Sym::Span((1, 2));
    match s {
        Sym::Nil => true,
        _ => false,
    }
}

// GUARD 4 — payload-binding guard (NESTED inline-AGGREGATE enum payload). M5.7e now
// LOWERS a ONE-LEVEL aggregate destructure (`Span((a, b))`), so the OLD one-level
// `Span(p)` case is no longer a meaningful negative — it was REPLACED with a
// NESTED aggregate: `Deep(((a, b), c))` destructures a `((i64, i64), i64)` payload,
// whose `(a, b)` sub-field is ITSELF an aggregate. M5.7e walks only ONE level of
// sub-field offsets (the bind path is `[outer_field, sub_field]`); a deeper path
// (the inner `(a, b)`) is explicitly out of scope, so it must STILL bail loud
// (nested aggregate-in-aggregate is future work). Reachable via `--target-fn
// neg_scalar_payload` (name kept stable for the regression harness; it now guards
// the NESTED aggregate, the one-level shape having become supported under M5.7e).
pub fn neg_scalar_payload(s: &Sym) -> bool {
    match s {
        Sym::Deep(((a, b), c)) => a + b > *c,
        _ => false,
    }
}

// GUARD 5 — scalar-deref guard (multi-level `**rr`). `rr: &&i64`, so `**rr`
// double-dereferences a pointer-to-pointer; `lower_place` peels ALL pointer
// layers, so loading the scalar through the outermost pointer would read the
// inner pointer's bits. Reachable via `--target-fn neg_multi_deref`.
pub fn neg_multi_deref(rr: &&i64, t: &Tree) -> bool {
    let v = **rr;
    match t {
        Tree::Leaf => v > 0,
        Tree::Node(_, _) => false,
    }
}

// GUARD 6 (M6) — tag-WIDTH cap. `Wide` is `repr(i128)` -> a 16-byte discriminant
// with NO trust-ir Load width (i8/i16/i32/i64 only); the faithful layout path must
// bail loud rather than mis-read a 16-byte tag. (The OLD i32-range guard is retired
// — a `repr(i64)` 2^32 discriminant now lowers correctly at an i64 tag.)
// Reachable via `--target-fn neg_wide_discr`.
pub fn neg_wide_discr(w: &Wide) -> bool {
    match w {
        Wide::Small => true,
        Wide::Huge => false,
    }
}

// GUARD 7 — collect_bindings guard (top-level `x @ Pat` whole-value binding at
// the ADT-match scrutinee). `x @ _` binds the WHOLE scrutinee pointer, which the
// field-offset binding machinery does not model. Reachable via `--target-fn
// neg_toplevel_atbind`.
pub fn neg_toplevel_atbind(t: &Tree) -> bool {
    match t {
        x @ _ => match x {
            Tree::Leaf => true,
            Tree::Node(_, _) => false,
        },
    }
}

fn main() {}
