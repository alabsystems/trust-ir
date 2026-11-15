// model.rs — pure (no-rustc) trust-ir construction of the M2 leaf class on the
// FAITHFUL Box/Arc heap layout, plus the differential harness.
//
// M1 modeled the recursive ADT as a tagged struct whose recursive payload slots
// were INLINE recursive struct values (an `Aggregate` in an SSA register). M2
// makes the layout match real `Box<Level>`/`Arc<Level>` memory:
//
//   struct MicroLevel { tag: i32 @0, p0: ptr @8, p1: ptr @16 }   // size 24, align 8
//
// A recursive payload field is a POINTER (`Ty::Ptr`, 8 bytes) to a heap-allocated
// child struct — exactly a `Box`. The predicate function takes a `Ptr` to the
// struct (the `&self` receiver), reads the discriminant with a typed
// `Load(I32)` through a field-offset GEP, `Switch`es on it, and recurses by
// `Load(Ptr)`-ing a child payload pointer and `Call`-ing itself on that pointer.
//
// To exercise this without a rustc invocation, each corpus value is lowered to a
// bespoke nullary "constructor" function that materializes the literal heap graph
// (`HeapAlloc` + field-offset `Store`s — the IR image of `Box::new(Max(.., ..))`)
// and then `Call`s the predicate on the root pointer, returning the bool. That is
// the faithful operational analog of `is_zero(&Max(Box::new(..), Box::new(..)))`.
//
// trust-ir extension this leans on: the interpreter now gives `Ty::Struct` a
// finite C-style byte layout (see crates/trust-ir/src/interpret.rs:
// `struct_layout`, and the `Ty::Struct` arms of byte_size/byte_align/
// encode_value/decode_value). Without it, `HeapAlloc(struct)` / `Store(field)` /
// `Load(field)` could not round-trip a struct through real memory.

use trust_ir::constant::Constant;
use trust_ir::inst::{AllocOrigin, SwitchCase};
use trust_ir::interpret::Interpreter;
use trust_ir::ty::{FieldDef, StructDef, Ty};
use trust_ir::value::{BlockId, FuncId, StructId, ValueId};
use trust_ir::Module;
use trust_ir_build::{validate_module, FunctionBuilder, ModuleBuilder};

/// A native MicroLevel oracle (matches the clean-kernel `Level` shape EXACTLY,
/// including `Param`):
///   Zero=0 | Succ(_)=1 | Max(l,l)=2 | IMax(l,l)=3 | Param(Name)=4
///
/// `Param` is the variant the M1 oracle missed: it returns `false` for BOTH
/// `is_zero` and `is_nonzero` (a universe parameter "might be 0 at runtime").
#[derive(Debug, Clone, PartialEq)]
pub enum Micro {
    Zero,
    Succ(Box<Micro>),
    Max(Box<Micro>, Box<Micro>),
    IMax(Box<Micro>, Box<Micro>),
    /// Universe parameter, carrying an opaque name id (irrelevant to the
    /// predicates; only the discriminant matters).
    Param(u64),
}

impl Micro {
    /// Discriminant tag, matching declaration order
    /// Zero=0, Succ=1, Max=2, IMax=3, Param=4.
    pub fn tag(&self) -> i128 {
        match self {
            Micro::Zero => 0,
            Micro::Succ(_) => 1,
            Micro::Max(..) => 2,
            Micro::IMax(..) => 3,
            Micro::Param(_) => 4,
        }
    }

    /// Native oracle: the exact semantics of clean-kernel `Level::is_zero`.
    pub fn is_zero(&self) -> bool {
        match self {
            Micro::Zero => true,
            Micro::Succ(_) | Micro::Param(_) => false,
            Micro::Max(l1, l2) => l1.is_zero() && l2.is_zero(),
            Micro::IMax(_, l2) => l2.is_zero(),
        }
    }

    /// Native oracle: the exact semantics of clean-kernel `Level::is_nonzero`.
    pub fn is_nonzero(&self) -> bool {
        match self {
            Micro::Zero | Micro::Param(_) => false,
            Micro::Succ(_) => true,
            Micro::Max(l1, l2) => l1.is_nonzero() || l2.is_nonzero(),
            Micro::IMax(_, l2) => l2.is_nonzero(),
        }
    }

    /// Native oracle for the M5.4 corpus `count_succ`: the total number of `Succ`
    /// nodes anywhere in the tree (a VALUE-producing i64 recursive fold). A
    /// `Succ` arm contributes 1 plus the count of its child; `Max`/`IMax` sum
    /// both children; `Zero`/`Param` are leaves contributing 0.
    pub fn count_succ(&self) -> i64 {
        match self {
            Micro::Zero | Micro::Param(_) => 0,
            Micro::Succ(inner) => 1 + inner.count_succ(),
            Micro::Max(l1, l2) | Micro::IMax(l1, l2) => l1.count_succ() + l2.count_succ(),
        }
    }
}

/// Which boolean predicate to build.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Pred {
    IsZero,
    IsNonzero,
}

/// M5.7b: a tiny expression-tree value MIXING an INLINE-SCALAR leaf payload
/// (`Lit(i64)`) with Box children (`Neg`/`Add`) — the microcosm of a kernel term
/// fold with a scalar leaf (`Expr::Var(i64)`). Mirrors the corpus `Val` enum and
/// drives the M5.7b differential / heap builder / native oracle.
///   Lit(i64)=0 | Neg(Box<Val>)=1 | Add(Box<Val>, Box<Val>)=2
#[derive(Debug, Clone, PartialEq)]
pub enum Val {
    /// A scalar leaf: the i64 is stored INLINE at the payload slot (NOT a Box).
    Lit(i64),
    Neg(Box<Val>),
    Add(Box<Val>, Box<Val>),
}

impl Val {
    /// Discriminant tag, matching declaration order Lit=0, Neg=1, Add=2.
    pub fn tag(&self) -> i128 {
        match self {
            Val::Lit(_) => 0,
            Val::Neg(_) => 1,
            Val::Add(..) => 2,
        }
    }

    /// Native oracle for the corpus `eval`: fold the expression tree to its i64
    /// value (wrapping arithmetic, mirroring the trust-ir `neg`/`add`).
    pub fn eval(&self) -> i64 {
        match self {
            Val::Lit(n) => *n,
            Val::Neg(a) => a.eval().wrapping_neg(),
            Val::Add(a, b) => a.eval().wrapping_add(b.eval()),
        }
    }
}

/// M5.7a: a lambda-calculus `Term` mirroring the corpus `Term` enum — the subject
/// of NESTED-CONSTRUCTOR match patterns (the canonical β-redex shape
/// `App(Lam(..), ..)`). Drives the M5.7a differential / heap builder / native
/// oracle. All three payload kinds are present: a SCALAR leaf (`Var(i64)`) and Box
/// children (`Lam`/`App`).
///   Var(i64)=0 | Lam(Box<Term>)=1 | App(Box<Term>, Box<Term>)=2
#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    Var(i64),
    Lam(Box<Term>),
    App(Box<Term>, Box<Term>),
}

impl Term {
    /// Discriminant tag, matching declaration order Var=0, Lam=1, App=2.
    pub fn tag(&self) -> i128 {
        match self {
            Term::Var(_) => 0,
            Term::Lam(_) => 1,
            Term::App(..) => 2,
        }
    }

    /// Native oracle for the corpus `is_beta_redex`: an `App` whose FUNCTION (first
    /// child) is a `Lam` — the one-level nested-constructor β-redex shape.
    pub fn is_beta_redex(&self) -> bool {
        match self {
            Term::App(f, _) => matches!(f.as_ref(), Term::Lam(_)),
            _ => false,
        }
    }

    /// Native oracle for the corpus `redex_body_is_var`: a β-redex (`App(Lam(b),_)`)
    /// whose lambda BODY `b` is a `Var`. Exercises the M5.7a inner binding + a
    /// further nested match on the bound child.
    pub fn redex_body_is_var(&self) -> bool {
        match self {
            Term::App(f, _) => match f.as_ref() {
                Term::Lam(b) => matches!(b.as_ref(), Term::Var(_)),
                _ => false,
            },
            _ => false,
        }
    }
}

/// M5.7e: a recursive enum whose `Span` variant carries an INLINE-AGGREGATE
/// payload — a single field that is a 2-tuple `(i64, i64)` — alongside a Box-child
/// recursive variant (`Cons`) and a leaf (`Nil`). Mirrors the corpus `Sym` enum and
/// drives the M5.7e differential / heap builder / native oracle.
///   Nil=0 | Span((i64, i64))=1 | Cons(Box<Sym>)=2
#[derive(Debug, Clone, PartialEq)]
pub enum Sym {
    Nil,
    /// An inline TUPLE payload: the two i64 sub-fields live INLINE within the
    /// variant's field slot (at the tuple's own sub-field offsets), NOT behind a Box.
    Span(i64, i64),
    Cons(Box<Sym>),
}

impl Sym {
    /// Discriminant tag, matching declaration order Nil=0, Span=1, Cons=2.
    pub fn tag(&self) -> i128 {
        match self {
            Sym::Nil => 0,
            Sym::Span(..) => 1,
            Sym::Cons(_) => 2,
        }
    }

    /// Native oracle for the corpus `sym_sum`: `Span((a, b))` sums its two inline
    /// sub-fields; `Cons(t)` recurses on the Box child; `Nil` is 0 (wrapping add,
    /// mirroring the trust-ir `add`).
    pub fn sym_sum(&self) -> i64 {
        match self {
            Sym::Nil => 0,
            Sym::Span(a, b) => a.wrapping_add(*b),
            Sym::Cons(t) => t.sym_sum(),
        }
    }
}

/// FIX 5: a recursive enum whose `Cell` variant carries an inline-aggregate of
/// NARROW sub-fields — a 2-tuple `(i32, i32)`, distinct from the I64 the other
/// builders hard-lock — alongside a Box-child recursive variant (`Next`) and a leaf
/// (`End`). Mirrors the corpus `Pair` enum. The sub-fields are written + read at
/// their REAL I32 width and i32-stride offsets (0 and 4 in the tuple), so a wrong
/// narrow Load/Store width (an I64 read would pull in the neighbour) or a wrong
/// offset would mis-sum — which the all-I64 `Sym` builder cannot expose.
///   End=0 | Cell((i32, i32))=1 | Next(Box<Pair>)=2
#[derive(Debug, Clone, PartialEq)]
pub enum Pair {
    End,
    /// An inline tuple of NARROW i32 sub-fields: i32 at the tuple's sub-offset 0,
    /// i32 at sub-offset 4.
    Cell(i32, i32),
    Next(Box<Pair>),
}

impl Pair {
    /// Discriminant tag, matching declaration order End=0, Cell=1, Next=2.
    pub fn tag(&self) -> i128 {
        match self {
            Pair::End => 0,
            Pair::Cell(..) => 1,
            Pair::Next(_) => 2,
        }
    }

    /// Native oracle for the corpus `pair_sum`: `Cell((a, b))` sums the two i32
    /// sub-fields at I32 width (wrapping, mirroring the trust-ir I32 add); `Next(t)`
    /// recurses on the Box child; `End` is 0. Returns the i32 result.
    pub fn pair_sum(&self) -> i32 {
        match self {
            Pair::End => 0,
            Pair::Cell(a, b) => a.wrapping_add(*b),
            Pair::Next(t) => t.pair_sum(),
        }
    }
}

// --- The faithful heap layout -------------------------------------------------
//
// M6: the heap builders now write the tag at the REAL width/offset and each
// child at the REAL per-variant field offset — driven by a `HeapLayout` so the
// bytes they Store match EXACTLY what the lowered predicate Loads. The
// interpreter `HeapAlloc`s UNINITIALIZED (`None`) memory, so an I64 tag Load over
// a 4-byte-written tag would read uninitialized bytes — hence the writer and the
// reader MUST agree on the tag WIDTH (this is why a faithful I64 tag is not
// optional: the corpus `Level` discriminant is an 8-byte Direct tag).
//
// The LEGACY default (`HeapLayout::legacy`) reproduces the original hand-coded
// shape `{ tag: i32 @0, p0: ptr @8, p1: ptr @16 }` for the pure (no-rustc) model
// tests, which build their OWN i32-tag predicate (`build_predicate_module`) and
// so stay self-consistent. The emitted-from-THIR differentials pass the REAL
// `HeapLayout` (from the frontend `EnumModel.layout`) so writer == real reader.
const TAG_OFFSET: i128 = 0;
/// Byte offset of recursive payload slot `i` (i in {0,1}).
fn payload_offset(i: usize) -> i128 {
    8 + 8 * (i as i128)
}

/// M6: a self-describing heap layout the heap builders Store against, so the
/// bytes match the lowered reader's Loads EXACTLY. For the recursive corpus enums
/// (Micro/Val/Term) variant 2 is the binary one (`Max`/`Add`/`App`), so two
/// child slots are enough; the per-variant tag value + field offsets come from
/// the real `layout_of` for the emitted differentials.
#[derive(Clone, Debug)]
pub struct HeapLayout {
    pub struct_id: StructId,
    pub tag_offset: i128,
    /// The tag Load/Store width (I8/I16/I32/I64) — the REAL discriminant width.
    pub tag_ir_ty: Ty,
    /// Per-variant tag value to Store: `Some(v)` for a Direct/niche-tagged
    /// variant; `None` for a niche UNTAGGED variant (Store NO niche tag — its
    /// payload field provides the discriminant). Indexed by the model's variant
    /// order.
    pub variant_tag: Vec<Option<i128>>,
    /// Per-variant field byte offsets, in field-index order. Indexed by variant.
    pub variant_field_offsets: Vec<Vec<i128>>,
    /// M6 NICHE: the value to Store at `tag_offset` for the niche UNTAGGED variant
    /// so the predicate's tag Load (which runs for EVERY input) reads an
    /// IN-BOUNDS, NON-NICHE value that decodes to the untagged variant. In a real
    /// niche `Level` this is the `Param(Name)` Arc pointer; here we use any
    /// integer distinct from every niche tag value. `None` for a Direct enum
    /// (every variant has an explicit tag, so there is no untagged word to fill).
    pub untagged_fill: Option<i128>,
}

impl HeapLayout {
    /// The original hand-coded shape `{ tag: i32 @0, p0: ptr @8, p1: ptr @16 }`
    /// with Direct tag values = the declaration index 0..N. Used by the pure
    /// model tests (which pair it with the i32-tag `build_predicate_module`), so
    /// those stay byte-self-consistent. `n_variants` is the enum's variant count.
    pub fn legacy(n_variants: usize) -> HeapLayout {
        HeapLayout {
            struct_id: StructId::new(0),
            tag_offset: TAG_OFFSET,
            tag_ir_ty: Ty::I32,
            variant_tag: (0..n_variants).map(|i| Some(i as i128)).collect(),
            variant_field_offsets: (0..n_variants)
                .map(|_| vec![payload_offset(0), payload_offset(1)])
                .collect(),
            untagged_fill: None,
        }
    }

    fn tag_for(&self, variant: usize) -> Option<i128> {
        self.variant_tag.get(variant).copied().flatten()
    }

    fn field_off(&self, variant: usize, field: usize) -> i128 {
        self.variant_field_offsets[variant][field]
    }

    /// M6: build a `HeapLayout` from the FAITHFUL frontend `EnumLayout` (derived
    /// from `tcx.layout_of`). The heap builders then Store the SAME bytes the
    /// lowered predicate Loads — tag width/offset, per-variant tag value (or none
    /// for the niche untagged variant), and per-variant field offsets. For a niche
    /// enum the untagged variant's niche word is filled with a NON-NICHE sentinel
    /// (`untagged_fill`) so the predicate's tag Load reads an in-bounds value that
    /// decodes to the untagged variant via the Switch default.
    pub fn from_enum_layout(el: &crate::EnumLayout) -> HeapLayout {
        let variant_tag: Vec<Option<i128>> =
            el.variants.iter().map(|v| v.switch_value).collect();
        let variant_field_offsets: Vec<Vec<i128>> = el
            .variants
            .iter()
            .map(|v| {
                // Ensure at least 2 slots so the binary-variant builders can
                // index field 1 even if a particular variant has fewer fields
                // (those extra entries are never used for that variant).
                let mut offs = v.field_offsets.clone();
                while offs.len() < 2 {
                    // A conventional 8-byte stride past the last known offset;
                    // never actually written for a variant that lacks the field.
                    let next = offs.last().copied().unwrap_or(el.tag_offset) + 8;
                    offs.push(next);
                }
                offs
            })
            .collect();
        // The untagged-fill sentinel: a value distinct from every niche tag value
        // so the default-route tag Load decodes to the untagged variant. We pick
        // (max niche value + 1) masked into range, falling back to a large
        // constant — it just must not collide with a niche case value.
        let untagged_fill = if el.is_niche() {
            let max_niche = el
                .variants
                .iter()
                .filter_map(|v| v.switch_value)
                .max()
                .unwrap_or(0);
            // A non-niche sentinel: one past the max niche value (the niche range
            // is contiguous from niche_start, so max+1 is outside it). For an
            // 8-byte tag this comfortably fits; it is a plausible "real pointer
            // low word" stand-in for the untagged variant's payload.
            Some(max_niche + 1)
        } else {
            None
        };
        HeapLayout {
            struct_id: StructId::new(0),
            tag_offset: el.tag_offset,
            tag_ir_ty: el.tag_ir_ty.clone(),
            variant_tag,
            variant_field_offsets,
            untagged_fill,
        }
    }
}

/// Register the faithful tagged-struct type in the module and return its id.
/// Payload slots are `Ty::Ptr` (a `Box`), NOT inline recursive structs. The tag
/// width follows the LEGACY i32 shape (the pure model tests' self-consistent
/// layout); the emitted differentials register their struct via the frontend's
/// `build_enum_model` (real tag width) instead.
fn add_microlevel_struct(mb: &mut ModuleBuilder) -> StructId {
    let sid = StructId::new(0);
    mb.add_struct(StructDef {
        id: sid,
        name: "MicroLevel".into(),
        fields: vec![
            FieldDef { name: "tag".into(), ty: Ty::I32, offset: None },
            FieldDef { name: "p0".into(), ty: Ty::Ptr, offset: None },
            FieldDef { name: "p1".into(), ty: Ty::Ptr, offset: None },
        ],
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    });
    sid
}

/// Emit, into the current block, a typed `Load` of the field at `byte_offset`
/// reached through an `I8`-pointee GEP (the design's "explicit byte-offset GEP
/// over an I8 pointee" for struct field access). Returns the loaded value.
fn load_field(fb: &mut FunctionBuilder<'_>, self_ptr: ValueId, byte_offset: i128, ty: Ty) -> ValueId {
    let off = fb.iconst(Ty::I64, byte_offset);
    let field_ptr = fb.gep_inbounds(Ty::I8, self_ptr, vec![off]);
    fb.load(ty, field_ptr)
}

/// Emit, into the current block, a `Store` of `value` (of type `ty`) into the
/// field at `byte_offset` of the struct at `self_ptr`.
fn store_field(
    fb: &mut FunctionBuilder<'_>,
    self_ptr: ValueId,
    byte_offset: i128,
    ty: Ty,
    value: ValueId,
) {
    let off = fb.iconst(Ty::I64, byte_offset);
    let field_ptr = fb.gep_inbounds(Ty::I8, self_ptr, vec![off]);
    fb.store(ty, field_ptr, value);
}

/// Build the trust-ir module for one predicate on the FAITHFUL heap layout.
///
/// Function 0 is the predicate `fn(ptr) -> bool` (its `&self` is a pointer to a
/// heap `MicroLevel`). Returns (Module, predicate FuncId, StructId, FuncTyId of
/// the predicate signature — needed to add per-input constructor functions).
///
/// CFG produced (for is_zero):
///   entry(self: ptr):
///     tag = load i32 (gep i8 self, 0)
///     switch tag { 0->b_zero 1->b_succ 2->b_max 3->b_imax 4->b_param } -> b_unreach
///   b_zero:  ret true
///   b_succ:  ret false
///   b_param: ret false
///   b_max:   l1 = load ptr (gep i8 self, 8) ; c0 = call self(l1)   ; l1.is_zero()
///            if c0 -> b_max_rhs else -> short(false)
///   b_max_rhs: l2 = load ptr (gep i8 self,16) ; c1 = call self(l2) ; -> join(c1)
///   b_imax:  l2 = load ptr (gep i8 self,16) ; c = call self(l2) ; ret c
///   b_unreach: unreachable
pub fn build_predicate_module(
    pred: Pred,
) -> Result<(Module, FuncId, StructId, trust_ir::value::FuncTyId), trust_ir_build::BuildError> {
    let name = match pred {
        Pred::IsZero => "is_zero",
        Pred::IsNonzero => "is_nonzero",
    };
    let mut mb = ModuleBuilder::new(format!("frontend::{name}"));
    let sid = add_microlevel_struct(&mut mb);

    // Signature: fn(ptr) -> bool. The &self receiver is a pointer (a Box/Arc).
    let sig = mb.add_func_type(vec![Ty::Ptr], vec![Ty::Bool]);
    let func_id = FuncId::new(0);

    {
        let mut fb = mb.function(name, sig);
        let entry = fb.create_block();
        let self_ptr = fb.add_block_param(entry, Ty::Ptr);

        let b_zero = fb.create_block();
        let b_succ = fb.create_block();
        let b_max = fb.create_block();
        let b_imax = fb.create_block();
        let b_param = fb.create_block();
        let b_unreach = fb.create_block();

        // entry: faithful discriminant read = typed Load(i32) through the tag GEP.
        fb.switch_to_block(entry);
        let tag = load_field(&mut fb, self_ptr, TAG_OFFSET, Ty::I32);
        let cases = vec![
            SwitchCase { value: Constant::Int(0), target: b_zero, args: vec![] },
            SwitchCase { value: Constant::Int(1), target: b_succ, args: vec![] },
            SwitchCase { value: Constant::Int(2), target: b_max, args: vec![] },
            SwitchCase { value: Constant::Int(3), target: b_imax, args: vec![] },
            SwitchCase { value: Constant::Int(4), target: b_param, args: vec![] },
        ];
        fb.switch(tag, cases, b_unreach, vec![]);

        let (zero_ret, succ_ret) = match pred {
            Pred::IsZero => (true, false),
            Pred::IsNonzero => (false, true),
        };

        // Leaf arms: constant returns. Param is a leaf returning false for BOTH
        // predicates (the bug M1's oracle could not see).
        fb.switch_to_block(b_zero);
        let cz = fb.bool_const(zero_ret);
        fb.ret(vec![cz]);

        fb.switch_to_block(b_succ);
        let cs = fb.bool_const(succ_ret);
        fb.ret(vec![cs]);

        fb.switch_to_block(b_param);
        let cp = fb.bool_const(false);
        fb.ret(vec![cp]);

        // b_max: && (is_zero) / || (is_nonzero) over the two child pointers.
        build_binary_recursion(&mut fb, pred, self_ptr, func_id, b_max);

        // b_imax: recurse on l2 only (payload slot 1, byte offset 16).
        fb.switch_to_block(b_imax);
        let l2 = load_field(&mut fb, self_ptr, payload_offset(1), Ty::Ptr);
        let imax_c = fb.call(func_id, vec![l2]);
        fb.ret(vec![imax_c]);

        fb.switch_to_block(b_unreach);
        fb.unreachable();

        fb.build();
    }

    Ok((mb.build()?, func_id, sid, sig))
}

/// Emit the Max-arm short-circuit recursion into `b_max`. The recursion passes
/// the child's HEAP POINTER (a `Load(ptr)` of the payload slot) to the same
/// FuncId — `l1.is_zero()` = "call the predicate on the pointed-to child".
fn build_binary_recursion(
    fb: &mut FunctionBuilder<'_>,
    pred: Pred,
    self_ptr: ValueId,
    func_id: FuncId,
    b_max: BlockId,
) {
    let rhs_block = fb.create_block();
    let short_block = fb.create_block();
    let join = fb.create_block();
    let join_param = fb.add_block_param(join, Ty::Bool);

    fb.switch_to_block(b_max);
    let l1 = load_field(fb, self_ptr, payload_offset(0), Ty::Ptr);
    let c0 = fb.call(func_id, vec![l1]);
    match pred {
        // && : if l1.is_zero() -> eval rhs else short(false)
        Pred::IsZero => fb.condbr(c0, rhs_block, vec![], short_block, vec![]),
        // || : if l1.is_nonzero() -> short(true) else eval rhs
        Pred::IsNonzero => fb.condbr(c0, short_block, vec![], rhs_block, vec![]),
    }

    fb.switch_to_block(short_block);
    let short_c = fb.bool_const(matches!(pred, Pred::IsNonzero));
    fb.br(join, vec![short_c]);

    fb.switch_to_block(rhs_block);
    let l2 = load_field(fb, self_ptr, payload_offset(1), Ty::Ptr);
    let c1 = fb.call(func_id, vec![l2]);
    fb.br(join, vec![c1]);

    fb.switch_to_block(join);
    fb.ret(vec![join_param]);
}

/// Recursively emit, into the current block of `fb`, the IR that builds the heap
/// graph for `m` (`HeapAlloc` of a MicroLevel struct + field-offset `Store`s of
/// its tag and child pointers — the IR image of `Box::new(..)`), returning the
/// `ValueId` of the root struct pointer. Children are allocated first and their
/// pointers stored into the parent's payload slots, exactly mirroring nested
/// `Box::new`.
fn build_heap_value(fb: &mut FunctionBuilder<'_>, lay: &HeapLayout, m: &Micro) -> ValueId {
    let p = fb.heap_alloc(Ty::Struct(lay.struct_id), None, None, AllocOrigin::RustHeap);
    let vi = m.tag() as usize;
    // Store the tag at the REAL width/offset. A niche UNTAGGED variant stores no
    // niche tag — instead it fills the niche word with an IN-BOUNDS, NON-NICHE
    // value (`untagged_fill`) so the predicate's tag Load (which runs for EVERY
    // input) reads a defined value that decodes to the untagged variant via the
    // Switch DEFAULT. (Reading an unwritten niche word would be an uninitialized
    // read — the interpreter `HeapAlloc`s `None` bytes.)
    match lay.tag_for(vi) {
        Some(tagv) => {
            let tag = fb.iconst(lay.tag_ir_ty.clone(), tagv);
            store_field(fb, p, lay.tag_offset, lay.tag_ir_ty.clone(), tag);
        }
        None => {
            if let Some(fill) = lay.untagged_fill {
                let tag = fb.iconst(lay.tag_ir_ty.clone(), fill);
                store_field(fb, p, lay.tag_offset, lay.tag_ir_ty.clone(), tag);
            }
        }
    }
    match m {
        Micro::Zero | Micro::Param(_) => {
            // Leaf: no recursive children. (Param's Name payload is irrelevant to
            // the predicate; only the discriminant matters. For a niche `Level`,
            // Param is the UNTAGGED variant — its niche word was filled above.)
        }
        Micro::Succ(inner) => {
            let c = build_heap_value(fb, lay, inner);
            store_field(fb, p, lay.field_off(vi, 0), Ty::Ptr, c);
        }
        Micro::Max(a, b) | Micro::IMax(a, b) => {
            let ca = build_heap_value(fb, lay, a);
            let cb = build_heap_value(fb, lay, b);
            store_field(fb, p, lay.field_off(vi, 0), Ty::Ptr, ca);
            store_field(fb, p, lay.field_off(vi, 1), Ty::Ptr, cb);
        }
    }
    p
}

/// Add a nullary "constructor + invoke" function to `mb`: it builds the heap
/// graph for `m`, calls the predicate `pred_func` on the root pointer, and
/// returns the resulting bool. This is the faithful IR analog of
/// `fn() -> bool { is_zero(&<m as Box-nested literal>) }`.
///
/// Public so the THIR-lowering driver (`main.rs`) can append runners to the
/// GENUINE module emitted from `tcx.thir_body` and differential-test the real
/// emitted predicate (not just this hand-mirrored one). `pred_func` must be the
/// `fn(ptr) -> bool` predicate, `sid` the MicroLevel `StructId` (the heap layout
/// `build_heap_value` allocates), and `nullary_bool_sig` a `fn() -> bool` type.
pub fn add_input_runner(
    mb: &mut ModuleBuilder,
    lay: &HeapLayout,
    m: &Micro,
    pred_func: FuncId,
    nullary_bool_sig: trust_ir::value::FuncTyId,
    name: &str,
) -> FuncId {
    let mut fb = mb.function(name, nullary_bool_sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let root = build_heap_value(&mut fb, lay, m);
    let result = fb.call(pred_func, vec![root]);
    fb.ret(vec![result]);
    fb.build()
}

/// M5.4: add a nullary "constructor + invoke" function that builds the heap
/// graph for `m` (the faithful Box-nested `Level` image via `build_heap_value`)
/// and calls a `fn(ptr) -> i64` function `target` on the root pointer, returning
/// the i64 result. The i64 analog of `add_input_runner`; used by the M5.4
/// differential to drive the THIR-lowered `count_succ` over real heap inputs.
/// `nullary_i64_sig` must be a `fn() -> i64` type registered in the module.
pub fn add_int_input_runner(
    mb: &mut ModuleBuilder,
    lay: &HeapLayout,
    m: &Micro,
    target: FuncId,
    nullary_i64_sig: trust_ir::value::FuncTyId,
    name: &str,
) -> FuncId {
    let mut fb = mb.function(name, nullary_i64_sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let root = build_heap_value(&mut fb, lay, m);
    let result = fb.call(target, vec![root]);
    fb.ret(vec![result]);
    fb.build()
}

/// M5.7b: recursively emit the IR that builds the heap graph for a `Val`. The
/// tagged struct is the SAME `{ tag: i32 @0, slot0 @8, slot1 @16 }` shape (the
/// `EnumModel` the frontend registers as `StructId(0)`), but the SLOTS are
/// written by FIELD KIND, NOT uniformly as pointers:
///   - `Lit(n)`: store the i64 INLINE at slot 0 (`Store(I64, @8)`) — there is no
///     Box; the value lives in the slot's 8 bytes. (This is the M5.7b payload the
///     emitted `eval` binds by ADDRESS and `*n`-Loads as an i64.)
///   - `Neg(a)`: alloc the child, store its POINTER at slot 0 (`Store(Ptr, @8)`).
///   - `Add(a, b)`: store the two child POINTERS at slots 0/1.
///
/// Mirrors `build_heap_value` for `Micro`, but with the inline-scalar `Lit` arm.
fn build_val_heap_value(fb: &mut FunctionBuilder<'_>, lay: &HeapLayout, v: &Val) -> ValueId {
    let p = fb.heap_alloc(Ty::Struct(lay.struct_id), None, None, AllocOrigin::RustHeap);
    let vi = v.tag() as usize;
    if let Some(tagv) = lay.tag_for(vi) {
        let tag = fb.iconst(lay.tag_ir_ty.clone(), tagv);
        store_field(fb, p, lay.tag_offset, lay.tag_ir_ty.clone(), tag);
    }
    match v {
        Val::Lit(n) => {
            // INLINE scalar: write the i64 directly into the slot (NO Box pointer).
            let nv = fb.iconst(Ty::I64, *n as i128);
            store_field(fb, p, lay.field_off(vi, 0), Ty::I64, nv);
        }
        Val::Neg(a) => {
            let ca = build_val_heap_value(fb, lay, a);
            store_field(fb, p, lay.field_off(vi, 0), Ty::Ptr, ca);
        }
        Val::Add(a, b) => {
            let ca = build_val_heap_value(fb, lay, a);
            let cb = build_val_heap_value(fb, lay, b);
            store_field(fb, p, lay.field_off(vi, 0), Ty::Ptr, ca);
            store_field(fb, p, lay.field_off(vi, 1), Ty::Ptr, cb);
        }
    }
    p
}

/// M5.7b: add a nullary "constructor + invoke" runner that builds the `Val` heap
/// graph (inline-scalar `Lit`, Box `Neg`/`Add`) and calls a `fn(ptr) -> i64`
/// `eval` on the root pointer, returning the i64. The `Val` analog of
/// `add_int_input_runner`; used by the M5.7b differential to drive the
/// THIR-lowered `eval` over real heap inputs. `nullary_i64_sig` must be a
/// `fn() -> i64` type registered in the module.
pub fn add_val_int_runner(
    mb: &mut ModuleBuilder,
    lay: &HeapLayout,
    v: &Val,
    target: FuncId,
    nullary_i64_sig: trust_ir::value::FuncTyId,
    name: &str,
) -> FuncId {
    let mut fb = mb.function(name, nullary_i64_sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let root = build_val_heap_value(&mut fb, lay, v);
    let result = fb.call(target, vec![root]);
    fb.ret(vec![result]);
    fb.build()
}

/// M5.7a: recursively emit the IR that builds the heap graph for a `Term` on the
/// SAME tagged struct `{ tag: i32 @0, slot0 @8, slot1 @16 }` (the `EnumModel` the
/// frontend registers as `StructId(0)`). Slots are written by FIELD KIND, exactly
/// as the frontend's nested-pattern lowering reads them:
///   - `Var(n)`: store the i64 INLINE at slot 0 (a scalar leaf, like `Val::Lit`).
///   - `Lam(b)`: alloc the child, store its POINTER at slot 0.
///   - `App(f, a)`: store the two child POINTERS at slots 0/1.
///
/// Mirrors `build_val_heap_value`/`build_heap_value`.
fn build_term_heap_value(fb: &mut FunctionBuilder<'_>, lay: &HeapLayout, t: &Term) -> ValueId {
    let p = fb.heap_alloc(Ty::Struct(lay.struct_id), None, None, AllocOrigin::RustHeap);
    let vi = t.tag() as usize;
    if let Some(tagv) = lay.tag_for(vi) {
        let tag = fb.iconst(lay.tag_ir_ty.clone(), tagv);
        store_field(fb, p, lay.tag_offset, lay.tag_ir_ty.clone(), tag);
    }
    match t {
        Term::Var(n) => {
            // INLINE scalar leaf: write the i64 directly into slot 0 (NO Box).
            let nv = fb.iconst(Ty::I64, *n as i128);
            store_field(fb, p, lay.field_off(vi, 0), Ty::I64, nv);
        }
        Term::Lam(b) => {
            let cb = build_term_heap_value(fb, lay, b);
            store_field(fb, p, lay.field_off(vi, 0), Ty::Ptr, cb);
        }
        Term::App(f, a) => {
            let cf = build_term_heap_value(fb, lay, f);
            let ca = build_term_heap_value(fb, lay, a);
            store_field(fb, p, lay.field_off(vi, 0), Ty::Ptr, cf);
            store_field(fb, p, lay.field_off(vi, 1), Ty::Ptr, ca);
        }
    }
    p
}

/// M5.7a: add a nullary "constructor + invoke" runner that builds the `Term` heap
/// graph and calls a `fn(ptr) -> bool` predicate (`is_beta_redex` /
/// `redex_body_is_var`) on the root pointer, returning the bool. The `Term`/bool
/// analog of `add_val_int_runner`; used by the M5.7a differential to drive the
/// THIR-lowered nested-pattern predicate over real heap graphs.
/// `nullary_bool_sig` must be a `fn() -> bool` type registered in the module.
pub fn add_term_bool_runner(
    mb: &mut ModuleBuilder,
    lay: &HeapLayout,
    t: &Term,
    target: FuncId,
    nullary_bool_sig: trust_ir::value::FuncTyId,
    name: &str,
) -> FuncId {
    let mut fb = mb.function(name, nullary_bool_sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let root = build_term_heap_value(&mut fb, lay, t);
    let result = fb.call(target, vec![root]);
    fb.ret(vec![result]);
    fb.build()
}

/// M5.7e: recursively emit the IR that builds the heap graph for a `Sym` on the
/// SAME tagged struct `{ tag, slot.. }` (the `EnumModel` the frontend registers as
/// `StructId(0)`). Slots are written by FIELD KIND, exactly as the frontend's
/// aggregate-payload lowering reads them:
///   - `Nil`: just the tag (a leaf).
///   - `Span(a, b)`: the variant's single field is an inline TUPLE `(i64, i64)`;
///     write the two i64 sub-fields at their REAL ABSOLUTE offsets
///     `span_sub_offsets[0]`/`[1]` (the tuple's offset within the variant + each
///     sub-field's offset within the tuple) — NO Box.
///   - `Cons(t)`: alloc the child, store its POINTER at the `Cons` field slot.
///
/// `span_sub_offsets` are the absolute byte offsets the FRONTEND derived for the two
/// `Span` sub-fields (computed from `tcx.layout_of`), so the bytes this writes match
/// EXACTLY what the lowered `sym_sum` Loads.
fn build_sym_heap_value(
    fb: &mut FunctionBuilder<'_>,
    lay: &HeapLayout,
    span_sub_offsets: [i128; 2],
    s: &Sym,
) -> ValueId {
    let p = fb.heap_alloc(Ty::Struct(lay.struct_id), None, None, AllocOrigin::RustHeap);
    let vi = s.tag() as usize;
    if let Some(tagv) = lay.tag_for(vi) {
        let tag = fb.iconst(lay.tag_ir_ty.clone(), tagv);
        store_field(fb, p, lay.tag_offset, lay.tag_ir_ty.clone(), tag);
    }
    match s {
        Sym::Nil => {}
        Sym::Span(a, b) => {
            // INLINE tuple: write each i64 sub-field at its absolute offset.
            let av = fb.iconst(Ty::I64, *a as i128);
            store_field(fb, p, span_sub_offsets[0], Ty::I64, av);
            let bv = fb.iconst(Ty::I64, *b as i128);
            store_field(fb, p, span_sub_offsets[1], Ty::I64, bv);
        }
        Sym::Cons(t) => {
            let c = build_sym_heap_value(fb, lay, span_sub_offsets, t);
            store_field(fb, p, lay.field_off(vi, 0), Ty::Ptr, c);
        }
    }
    p
}

/// M5.7e: add a nullary "constructor + invoke" runner that builds the `Sym` heap
/// graph (inline-tuple `Span`, Box `Cons`, leaf `Nil`) and calls a `fn(ptr) -> i64`
/// `sym_sum` on the root pointer, returning the i64. The `Sym` analog of
/// `add_val_int_runner`; used by the M5.7e differential to drive the THIR-lowered
/// `sym_sum` over real heap inputs. `nullary_i64_sig` must be a `fn() -> i64` type.
/// `span_sub_offsets` are the FRONTEND-derived absolute offsets of `Span`'s two
/// inline sub-fields (so the writer matches the reader exactly).
#[allow(clippy::too_many_arguments)]
pub fn add_sym_int_runner(
    mb: &mut ModuleBuilder,
    lay: &HeapLayout,
    span_sub_offsets: [i128; 2],
    s: &Sym,
    target: FuncId,
    nullary_i64_sig: trust_ir::value::FuncTyId,
    name: &str,
) -> FuncId {
    let mut fb = mb.function(name, nullary_i64_sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let root = build_sym_heap_value(&mut fb, lay, span_sub_offsets, s);
    let result = fb.call(target, vec![root]);
    fb.ret(vec![result]);
    fb.build()
}

/// FIX 5: recursively build the `Pair` heap graph, writing the `Cell` tuple's two
/// NARROW sub-fields at their REAL I32 width and i32-stride offsets — so the heap
/// builder (the differential's WRITE side) exercises a width DISTINCT from I64, not
/// the uniform-I64 hard-lock the other builders use. `cell_subs` is the
/// FRONTEND-derived [(abs_offset, width)] of `Cell`'s two sub-fields, so the writer
/// matches the reader exactly.
fn build_pair_heap_value(
    fb: &mut FunctionBuilder<'_>,
    lay: &HeapLayout,
    cell_subs: &[(i128, Ty); 2],
    p_val: &Pair,
) -> ValueId {
    let p = fb.heap_alloc(Ty::Struct(lay.struct_id), None, None, AllocOrigin::RustHeap);
    let vi = p_val.tag() as usize;
    if let Some(tagv) = lay.tag_for(vi) {
        let tag = fb.iconst(lay.tag_ir_ty.clone(), tagv);
        store_field(fb, p, lay.tag_offset, lay.tag_ir_ty.clone(), tag);
    }
    match p_val {
        Pair::End => {}
        Pair::Cell(a, b) => {
            // DISTINCT widths: the i8 at its width/offset, the i64 at its
            // width/offset. (`iconst` carries the value; the Store width is what
            // pins how many bytes land — a wrong width here would desync the
            // reader's narrow Load.)
            let (off0, w0) = &cell_subs[0];
            let av = fb.iconst(w0.clone(), *a as i128);
            store_field(fb, p, *off0, w0.clone(), av);
            let (off1, w1) = &cell_subs[1];
            let bv = fb.iconst(w1.clone(), *b as i128);
            store_field(fb, p, *off1, w1.clone(), bv);
        }
        Pair::Next(t) => {
            let c = build_pair_heap_value(fb, lay, cell_subs, t);
            store_field(fb, p, lay.field_off(vi, 0), Ty::Ptr, c);
        }
    }
    p
}

/// FIX 5: add a nullary "constructor + invoke" runner that builds the `Pair` heap
/// graph (narrow-width inline tuple `Cell`, Box `Next`, leaf `End`) and calls the
/// `fn(ptr) -> i32` `pair_sum` on the root pointer, returning the i32. The runner's
/// own signature (`nullary_i32_sig`) must match `pair_sum`'s i32 return.
#[allow(clippy::too_many_arguments)]
pub fn add_pair_int_runner(
    mb: &mut ModuleBuilder,
    lay: &HeapLayout,
    cell_subs: &[(i128, Ty); 2],
    p_val: &Pair,
    target: FuncId,
    nullary_i64_sig: trust_ir::value::FuncTyId,
    name: &str,
) -> FuncId {
    let mut fb = mb.function(name, nullary_i64_sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let root = build_pair_heap_value(&mut fb, lay, cell_subs, p_val);
    let result = fb.call(target, vec![root]);
    fb.ret(vec![result]);
    fb.build()
}

/// Build a full module for `pred` containing the predicate plus one nullary
/// runner per corpus value, returning (Module, predicate FuncId, runner ids
/// aligned with `cases`).
fn build_differential_module(
    pred: Pred,
    cases: &[Micro],
) -> Result<(Module, FuncId, Vec<FuncId>), trust_ir_build::BuildError> {
    let name = match pred {
        Pred::IsZero => "is_zero",
        Pred::IsNonzero => "is_nonzero",
    };
    let mut mb = ModuleBuilder::new(format!("frontend::{name}::heap"));
    let _sid = add_microlevel_struct(&mut mb);
    let bool_sig_pred = mb.add_func_type(vec![Ty::Ptr], vec![Ty::Bool]);
    let pred_func = FuncId::new(0);
    {
        // Re-emit the predicate body (same as build_predicate_module but into
        // this shared module, so the runners can Call it).
        emit_predicate_body(&mut mb, pred, name, bool_sig_pred);
    }
    // Nullary runner signature: fn() -> bool.
    let runner_sig = mb.add_func_type(vec![], vec![Ty::Bool]);
    // The LEGACY i32-tag layout, self-consistent with `emit_predicate_body`'s
    // i32-tag reader above (the pure no-rustc model tests).
    let lay = HeapLayout::legacy(5);
    let mut runners = Vec::with_capacity(cases.len());
    for (i, m) in cases.iter().enumerate() {
        runners.push(add_input_runner(&mut mb, &lay, m, pred_func, runner_sig, &format!("run_{i}")));
    }
    Ok((mb.build()?, pred_func, runners))
}

/// Emit just the predicate function body into an existing ModuleBuilder (shared
/// with `build_predicate_module`'s CFG, factored out so the differential module
/// can host both the predicate and the per-input runners).
fn emit_predicate_body(mb: &mut ModuleBuilder, pred: Pred, name: &str, sig: trust_ir::value::FuncTyId) {
    let func_id = FuncId::new(0);
    let mut fb = mb.function(name, sig);
    let entry = fb.create_block();
    let self_ptr = fb.add_block_param(entry, Ty::Ptr);

    let b_zero = fb.create_block();
    let b_succ = fb.create_block();
    let b_max = fb.create_block();
    let b_imax = fb.create_block();
    let b_param = fb.create_block();
    let b_unreach = fb.create_block();

    fb.switch_to_block(entry);
    let tag = load_field(&mut fb, self_ptr, TAG_OFFSET, Ty::I32);
    let cases = vec![
        SwitchCase { value: Constant::Int(0), target: b_zero, args: vec![] },
        SwitchCase { value: Constant::Int(1), target: b_succ, args: vec![] },
        SwitchCase { value: Constant::Int(2), target: b_max, args: vec![] },
        SwitchCase { value: Constant::Int(3), target: b_imax, args: vec![] },
        SwitchCase { value: Constant::Int(4), target: b_param, args: vec![] },
    ];
    fb.switch(tag, cases, b_unreach, vec![]);

    let (zero_ret, succ_ret) = match pred {
        Pred::IsZero => (true, false),
        Pred::IsNonzero => (false, true),
    };

    fb.switch_to_block(b_zero);
    let cz = fb.bool_const(zero_ret);
    fb.ret(vec![cz]);

    fb.switch_to_block(b_succ);
    let cs = fb.bool_const(succ_ret);
    fb.ret(vec![cs]);

    fb.switch_to_block(b_param);
    let cp = fb.bool_const(false);
    fb.ret(vec![cp]);

    build_binary_recursion(&mut fb, pred, self_ptr, func_id, b_max);

    fb.switch_to_block(b_imax);
    let l2 = load_field(&mut fb, self_ptr, payload_offset(1), Ty::Ptr);
    let imax_c = fb.call(func_id, vec![l2]);
    fb.ret(vec![imax_c]);

    fb.switch_to_block(b_unreach);
    fb.unreachable();

    fb.build();
}

/// Differential-test a GENUINE THIR-emitted predicate. Given the UNBUILT
/// `ModuleBuilder` from `lower_fn_to_builder` (predicate = `FuncId(0)`,
/// `fn(ptr) -> bool`, MicroLevel struct = `StructId(0)`) and the predicate name
/// (`is_zero`/`is_nonzero`), append one heap-constructing runner per corpus
/// value, build + validate the module, and interpret each runner against the
/// native oracle. This tests the REAL emitted bytes, not the hand-mirrored
/// `build_predicate_module`.
pub fn run_emitted_differential(
    mut mb: ModuleBuilder,
    pred_func: FuncId,
    name: &str,
    lay: &HeapLayout,
) -> Result<Option<DifferentialReport>, trust_ir_build::BuildError> {
    let pred = match name {
        "is_zero" => Pred::IsZero,
        "is_nonzero" => Pred::IsNonzero,
        _ => return Ok(None),
    };
    let cases = corpus();
    let nullary_bool = mb.add_func_type(vec![], vec![Ty::Bool]);
    let runners: Vec<FuncId> = cases
        .iter()
        .enumerate()
        .map(|(i, m)| add_input_runner(&mut mb, lay, m, pred_func, nullary_bool, &format!("run_{i}")))
        .collect();
    let module = mb.build()?;
    let verrs = validate_module(&module);

    let mut n_match = 0usize;
    let mut first_mismatch = None;
    let mut param_total = 0usize;
    let mut param_match = 0usize;
    for (m, runner) in cases.iter().zip(&runners) {
        let oracle = match pred {
            Pred::IsZero => m.is_zero(),
            Pred::IsNonzero => m.is_nonzero(),
        };
        let is_param = mentions_param(m);
        if is_param {
            param_total += 1;
        }
        match interp_runner(&module, *runner) {
            Ok(got) if got == oracle => {
                n_match += 1;
                if is_param {
                    param_match += 1;
                }
            }
            Ok(got) => {
                if first_mismatch.is_none() {
                    first_mismatch = Some(format!("{m:?}: interp={got} oracle={oracle}"));
                }
            }
            Err(e) => {
                if first_mismatch.is_none() {
                    first_mismatch = Some(format!("{m:?}: {e}"));
                }
            }
        }
    }
    Ok(Some(DifferentialReport {
        pred,
        validate_errors: verrs.len(),
        n_match,
        n_total: cases.len(),
        param_match,
        param_total,
        first_mismatch,
    }))
}

/// Run the interpreter on `runner` (a nullary fn building the heap graph and
/// calling the predicate), returning the bool result.
pub fn interp_runner(module: &Module, runner: FuncId) -> Result<bool, String> {
    let interp = Interpreter::with_module(module);
    let outcome = interp
        .execute_func(runner, [])
        .map_err(|e| format!("interp error: {e:?}"))?;
    let ret = outcome
        .returns
        .first()
        .ok_or_else(|| "no return value".to_string())?;
    ret.as_bool().ok_or_else(|| format!("non-bool return: {ret:?}"))
}

/// A representative corpus exercising every variant (incl. Param), nesting, and
/// both short-circuit directions.
pub fn corpus() -> Vec<Micro> {
    let z = || Micro::Zero;
    let s = |m: Micro| Micro::Succ(Box::new(m));
    let mx = |a: Micro, b: Micro| Micro::Max(Box::new(a), Box::new(b));
    let im = |a: Micro, b: Micro| Micro::IMax(Box::new(a), Box::new(b));
    let pm = |n: u64| Micro::Param(n);
    vec![
        z(),
        s(z()),
        s(s(z())),
        pm(0),                        // Param: is_zero=false, is_nonzero=false
        pm(7),
        mx(z(), z()),                 // is_zero true
        mx(z(), s(z())),              // is_zero false (rhs nonzero) — && short-circuit
        mx(s(z()), z()),              // is_zero false (lhs nonzero) — short at lhs
        mx(s(z()), s(z())),
        mx(z(), pm(1)),               // Param under Max (neither zero nor nonzero on rhs)
        mx(pm(2), pm(3)),             // both Param
        im(z(), z()),                 // imax(_,0)=0 -> is_zero true
        im(s(z()), z()),              // imax(succ,0)=0 -> is_zero true (lhs ignored!)
        im(z(), s(z())),              // imax(_,succ) -> is_zero false
        im(s(s(z())), s(z())),
        im(pm(4), z()),               // imax(param, 0) -> is_zero true (lhs ignored)
        im(pm(5), pm(6)),             // imax(param, param) -> is_zero false, is_nonzero false
        mx(im(z(), z()), z()),        // nested
        mx(z(), im(s(z()), s(z()))),
        mx(pm(8), s(z())),            // is_nonzero: lhs param(false) || rhs succ(true) = true
        s(pm(9)),                     // Succ(Param): is_nonzero true, is_zero false
    ]
}

/// Run the full differential for one predicate: build the shared heap module
/// (predicate + per-input runners), validate, interpret each runner vs the
/// native oracle. Returns a structured report.
pub fn run_differential(pred: Pred) -> Result<DifferentialReport, trust_ir_build::BuildError> {
    let cases = corpus();
    let (module, _pred_func, runners) = build_differential_module(pred, &cases)?;
    let verrs = validate_module(&module);
    let mut n_match = 0usize;
    let mut first_mismatch = None;
    let mut param_total = 0usize;
    let mut param_match = 0usize;
    for (m, runner) in cases.iter().zip(&runners) {
        let oracle = match pred {
            Pred::IsZero => m.is_zero(),
            Pred::IsNonzero => m.is_nonzero(),
        };
        let is_param_case = mentions_param(m);
        if is_param_case {
            param_total += 1;
        }
        match interp_runner(&module, *runner) {
            Ok(got) if got == oracle => {
                n_match += 1;
                if is_param_case {
                    param_match += 1;
                }
            }
            Ok(got) => {
                if first_mismatch.is_none() {
                    first_mismatch = Some(format!("{m:?}: interp={got} oracle={oracle}"));
                }
            }
            Err(e) => {
                if first_mismatch.is_none() {
                    first_mismatch = Some(format!("{m:?}: {e}"));
                }
            }
        }
    }
    Ok(DifferentialReport {
        pred,
        validate_errors: verrs.len(),
        n_match,
        n_total: cases.len(),
        param_match,
        param_total,
        first_mismatch,
    })
}

/// Does this value mention a `Param` anywhere (for Param-coverage accounting)?
fn mentions_param(m: &Micro) -> bool {
    match m {
        Micro::Param(_) => true,
        Micro::Zero => false,
        Micro::Succ(a) => mentions_param(a),
        Micro::Max(a, b) | Micro::IMax(a, b) => mentions_param(a) || mentions_param(b),
    }
}

#[derive(Debug)]
pub struct DifferentialReport {
    pub pred: Pred,
    pub validate_errors: usize,
    pub n_match: usize,
    pub n_total: usize,
    /// How many Param-bearing cases matched the oracle (M1 oracle missed these).
    pub param_match: usize,
    pub param_total: usize,
    pub first_mismatch: Option<String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn is_zero_differential_heap() {
        let r = run_differential(Pred::IsZero).expect("the differential module builds");
        assert_eq!(r.validate_errors, 0, "validate errors: {r:?}");
        assert_eq!(r.n_match, r.n_total, "mismatch: {:?}", r.first_mismatch);
        assert!(r.param_total > 0, "corpus must cover Param");
        assert_eq!(r.param_match, r.param_total, "Param cases must all match");
    }

    #[test]
    fn is_nonzero_differential_heap() {
        let r = run_differential(Pred::IsNonzero).expect("the differential module builds");
        assert_eq!(r.validate_errors, 0, "validate errors: {r:?}");
        assert_eq!(r.n_match, r.n_total, "mismatch: {:?}", r.first_mismatch);
        assert!(r.param_total > 0, "corpus must cover Param");
        assert_eq!(r.param_match, r.param_total, "Param cases must all match");
    }

    /// The standalone single-predicate module (no runners) also validates with
    /// zero errors — this is the artifact the THIR lowering targets.
    #[test]
    fn predicate_module_validates() {
        for pred in [Pred::IsZero, Pred::IsNonzero] {
            let (module, _f, _sid, _sig) =
                build_predicate_module(pred).expect("the predicate module builds");
            let verrs = validate_module(&module);
            assert_eq!(verrs.len(), 0, "{pred:?} validate: {verrs:?}");
        }
    }
}
