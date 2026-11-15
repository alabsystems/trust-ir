// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Subset condition 6's `Char`-by-value walk, in both spellings, against the
//! walk it replaced.
//!
//! A `Load` / `AtomicLoad` / `LoadSlot` at a type that carries a `Char` by
//! value is outside the subset, resolved through the module's member tables.
//! Both spellings walked that with a native recursion cut off at 24 levels,
//! answering "carries a `Char`" when the budget ran out: a dangling or cyclic
//! table failed closed, but so did every char-free type 24 levels deep, and a
//! shared sub-type was walked once per path (2^d through `P{k+1} = {Pk,
//! Pk}`). Now the core classifier (`ConformanceSubset`) decides it with
//! `trust_ir::reach`'s memo (cycles found as strongly connected components)
//! and the mirror (`subset::CharCarriers`) with a whole-module summary
//! (cycles found by peeling), with no depth limit.
//!
//! The oracle is the old walk VERBATIM ([`old_walk`]) given a budget no
//! acyclic path can exhaust (every type spelled in the module, plus the
//! question, plus two): it then answers "carries" exactly when a `Char`, a
//! dangling reference or a cycle is reachable, which is what the old walk
//! answered as its budget grows. On random modules (missing, duplicate and
//! out-of-place ids, cycles through every kind) every load is judged by the
//! classifier's one-shot entry and module walk, the mirror's one-shot entry,
//! summary and module walk, and must equal the oracle; the old 24-level
//! verdict may differ only by refusing. The deep shapes run at 10^5 levels
//! on a 256 KiB stack, the mirror's work counter held linear first at 2000.

use trust_ir::ty::{ClosureTy, EnumDef, EnumVariant, FieldDef, RecordDef, SetRepr, StructDef};
use trust_ir::{
    Block, BlockId, ClosureTyId, ConformanceSubset, EnumId, FuncId, FuncTy, FuncTyId, Function,
    Inst, InstrNode, Module, PredId, RecordId, StructId, Ty, TyId, ValueId,
};
use trust_ir_conformance::subset::{
    CharCarriers, char_origin_violation_in, module_subset_violations,
};

// ---------------------------------------------------------------------------
// The oracle: the walk both spellings used, verbatim, with its budget a
// parameter
// ---------------------------------------------------------------------------

/// `trust_ir_conformance::subset::ty_carries_char_value_in` before this
/// change (the classifier's was the same text), plus one arm that postdates
/// it: a `Tensor` (the tensor region, PKG-U13a) holds its element inline, so
/// the walk descends into it exactly as into a `Vector`'s lane.
fn old_walk(module: &Module, ty: &Ty, depth: u32) -> bool {
    let Some(depth) = depth.checked_sub(1) else {
        return true;
    };
    let resolve = |id| module.ty(id).is_none_or(|t| old_walk(module, t, depth));
    match ty {
        Ty::Char => true,
        Ty::Vector(inner, _) | Ty::Tensor(inner, _) => old_walk(module, inner, depth),
        Ty::Tuple(xs) => xs.iter().any(|t| old_walk(module, t, depth)),
        Ty::Array(elem, _) | Ty::Sequence(elem) | Ty::Set(elem, _) => resolve(*elem),
        Ty::Refine(base, _) => resolve(*base),
        Ty::Struct(id) => module
            .struct_def(*id)
            .is_none_or(|def| def.fields.iter().any(|f| old_walk(module, &f.ty, depth))),
        Ty::Record(id) => module
            .record_def(*id)
            .is_none_or(|def| def.fields.iter().any(|f| old_walk(module, &f.ty, depth))),
        Ty::Enum(id) => module.enum_def(*id).is_none_or(|def| {
            def.variants
                .iter()
                .flat_map(|variant| variant.fields.iter())
                .any(|t| old_walk(module, t, depth))
        }),
        Ty::Closure(id) => module
            .closure_type(*id)
            .is_none_or(|def| def.captures.iter().any(|t| old_walk(module, t, depth))),
        _ => false,
    }
}

/// The old budget.
const OLD_BUDGET: u32 = 24;

/// Inline type nodes in one spelling.
fn spelled(ty: &Ty) -> u32 {
    let mut count = 0;
    ty.visit_types(|_| count += 1);
    count
}

/// A budget no acyclic path from `ty` can exhaust: each step of a path
/// enters one spelled type node, and an acyclic path enters each table
/// node's spelling at most once.
fn unbounded(module: &Module, ty: &Ty) -> u32 {
    let tables: u32 = module.types.iter().map(spelled).sum::<u32>()
        + module
            .structs
            .iter()
            .flat_map(|def| &def.fields)
            .map(|field| spelled(&field.ty))
            .sum::<u32>()
        + module
            .enums
            .iter()
            .flat_map(|def| &def.variants)
            .flat_map(|variant| &variant.fields)
            .map(spelled)
            .sum::<u32>()
        + module
            .records
            .iter()
            .flat_map(|def| &def.fields)
            .map(|field| spelled(&field.ty))
            .sum::<u32>()
        + module
            .closure_types
            .iter()
            .flat_map(|closure| &closure.captures)
            .map(spelled)
            .sum::<u32>();
    tables + spelled(ty) + 2
}

// ---------------------------------------------------------------------------
// Every spelling of the verdict
// ---------------------------------------------------------------------------

const CHAR_LOAD: &str = "may not be READ FROM MEMORY";

fn load(ty: Ty) -> Inst {
    Inst::Load {
        ty,
        ptr: ValueId::new(0),
        volatile: false,
        align: None,
    }
}

/// `module` with one function loading each of `types` in turn.
fn loading(module: &Module, types: &[Ty]) -> Module {
    let mut module = module.clone();
    let ft = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(module.functions.len() as u32);
    let mut func = Function::new(id, "loads", ft, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::Ptr);
    for (index, ty) in types.iter().enumerate() {
        block
            .body
            .push(InstrNode::new(load(ty.clone())).with_result(ValueId::new(index as u32 + 1)));
    }
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    func.blocks.push(block);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

/// Each load's condition-6 verdict from both module walks.
fn module_walks(module: &Module, types: &[Ty]) -> (Vec<bool>, Vec<bool>) {
    let loads = loading(module, types);
    let mut classifier = vec![false; types.len()];
    if let Err(violations) = loads.check_conformance_subset() {
        for violation in violations {
            if violation.reason.contains(CHAR_LOAD)
                && let Some(index) = violation.instruction_index
            {
                classifier[index] = true;
            }
        }
    }
    let mirror_violations = module_subset_violations(&loads);
    let mirror = (0..types.len())
        .map(|index| {
            let at = format!("inst #{index}: Inst::Load: ");
            mirror_violations
                .iter()
                .any(|violation| violation.contains(&at) && violation.contains(CHAR_LOAD))
        })
        .collect();
    (classifier, mirror)
}

#[derive(Debug, Default)]
struct Census {
    loads: usize,
    carried: usize,
    clean: usize,
    /// The old budget refused a char-free type.
    cut_off: usize,
}

/// Every spelling of every load's verdict equals the oracle's.
fn compare(label: &str, module: &Module, types: &[Ty], census: &mut Census) {
    let summary = CharCarriers::of(module);
    let (classifier_walk, mirror_walk) = module_walks(module, types);
    for (index, ty) in types.iter().enumerate() {
        let want = old_walk(module, ty, unbounded(module, ty));
        let label = format!("{label}: load {ty:?}");
        assert_eq!(
            ConformanceSubset::char_origin_excluded_in(module, &load(ty.clone())).is_some(),
            want,
            "{label}: classifier, one shot"
        );
        assert_eq!(
            classifier_walk[index], want,
            "{label}: classifier, module walk"
        );
        assert_eq!(
            char_origin_violation_in(module, &load(ty.clone())).is_some(),
            want,
            "{label}: mirror, one shot"
        );
        assert_eq!(summary.carries(ty), want, "{label}: mirror summary");
        assert_eq!(mirror_walk[index], want, "{label}: mirror, module walk");
        // The old budget only ever refused more.
        let old = old_walk(module, ty, OLD_BUDGET);
        assert!(old || !want, "{label}: the old walk admitted it");
        census.loads += 1;
        census.carried += usize::from(want);
        census.clean += usize::from(!want);
        census.cut_off += usize::from(old && !want);
    }
}

// ---------------------------------------------------------------------------
// Random modules
// ---------------------------------------------------------------------------

/// splitmix64.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: u64) -> u64 {
        if n == 0 { 0 } else { self.next() % n }
    }

    fn chance(&mut self, percent: u64) -> bool {
        self.below(100) < percent
    }
}

struct Gen {
    rng: Rng,
    types: u32,
    structs: u32,
    enums: u32,
    records: u32,
    closures: u32,
    /// Percent of leaves that are a `Char`.
    chars: u64,
}

impl Gen {
    /// An id up to one past the table (missing).
    fn id(&mut self, n: u32) -> u32 {
        self.rng.below(u64::from(n) + 1) as u32
    }

    fn leaf(&mut self) -> Ty {
        if self.rng.chance(self.chars) {
            return Ty::Char;
        }
        match self.rng.below(10) {
            0 => Ty::U8,
            1 => Ty::U64,
            2 => Ty::Bool,
            3 => Ty::Unit,
            4 => Ty::Ptr,
            5 => Ty::I32,
            6 => Ty::Func(FuncTyId::new(0)),
            7 => Ty::FatPtr(trust_ir::FatPtrKind::Str),
            8 => Ty::Never,
            _ => Ty::F64,
        }
    }

    fn ty(&mut self, depth: u32) -> Ty {
        match self.rng.below(100) {
            0..=29 => self.leaf(),
            30..=44 => Ty::Struct(StructId::new(self.id(self.structs))),
            45..=52 => Ty::Enum(EnumId::new(self.id(self.enums))),
            53..=57 => Ty::Record(RecordId::new(self.id(self.records))),
            58..=61 => Ty::Closure(ClosureTyId::new(self.id(self.closures))),
            62..=67 => Ty::Array(TyId::new(self.id(self.types)), self.rng.below(3)),
            68..=69 => Ty::Sequence(TyId::new(self.id(self.types))),
            70..=71 => Ty::Set(TyId::new(self.id(self.types)), SetRepr::Bitset),
            72..=73 => Ty::Refine(TyId::new(self.id(self.types)), PredId::new(0)),
            74..=80 if depth > 0 => {
                let inner = Box::new(self.ty(depth - 1));
                match self.rng.below(5) {
                    0 => Ty::Ref(inner),
                    1 => Ty::RefMut(inner),
                    2 => Ty::PtrConst(inner),
                    3 => Ty::PtrMut(inner),
                    _ => Ty::Rc(inner),
                }
            }
            81..=87 if depth > 0 => Ty::Vector(Box::new(self.ty(depth - 1)), 2),
            88..=99 if depth > 0 => {
                let n = self.rng.below(4);
                Ty::Tuple((0..n).map(|_| self.ty(depth - 1)).collect())
            }
            _ => self.leaf(),
        }
    }

    fn tys(&mut self, max: u64) -> Vec<Ty> {
        let n = self.rng.below(max + 1);
        (0..n).map(|_| self.ty(2)).collect()
    }

    /// The id of row `index` of a table of `len`: its position, or now and
    /// then a duplicate of an earlier one, the NEXT row's id (so that row
    /// is a duplicate at its own position) or one past the table.
    fn row_id(&mut self, index: u32, len: u32) -> u32 {
        match self.rng.below(100) {
            0..=7 if index > 0 => self.rng.below(u64::from(index)) as u32,
            8..=13 => index + 1,
            14..=16 => len + index,
            _ => index,
        }
    }
}

fn random_module(seed: u64) -> (Module, Vec<Ty>) {
    let mut rng = Rng(seed);
    let size = 1 + rng.below(7) as u32;
    let mut g = Gen {
        rng: Rng(seed ^ 0xc4a7),
        types: size,
        structs: size,
        enums: 1 + rng.below(u64::from(size)) as u32,
        records: rng.below(3) as u32,
        closures: rng.below(3) as u32,
        chars: [0, 3, 8, 20][rng.below(4) as usize],
    };
    let mut module = Module::new("chars");
    module.func_types.push(FuncTy {
        params: vec![],
        returns: vec![],
        abi: None,
        is_vararg: false,
    });
    for _ in 0..g.types {
        let ty = g.ty(2);
        module.types.push(ty);
    }
    for index in 0..g.structs {
        let id = g.row_id(index, g.structs);
        let fields = g
            .tys(3)
            .into_iter()
            .map(|ty| FieldDef {
                name: "f".into(),
                ty,
                offset: None,
            })
            .collect();
        module.structs.push(StructDef {
            id: StructId::new(id),
            name: format!("S{index}"),
            fields,
            size: None,
            align: None,
            repr: Default::default(),
            origin: None,
        });
    }
    for index in 0..g.enums {
        let id = g.row_id(index, g.enums);
        let variants = (0..1 + g.rng.below(3))
            .map(|v| EnumVariant {
                name: format!("V{v}"),
                fields: g.tys(2),
                field_names: Vec::new(),
            })
            .collect();
        module
            .enums
            .push(EnumDef::new(EnumId::new(id), format!("E{index}"), variants));
    }
    for index in 0..g.records {
        let id = g.row_id(index, g.records);
        let fields = g
            .tys(2)
            .into_iter()
            .map(|ty| FieldDef {
                name: "r".into(),
                ty,
                offset: None,
            })
            .collect();
        module.records.push(RecordDef {
            id: RecordId::new(id),
            name: format!("R{index}"),
            fields,
        });
    }
    for _ in 0..g.closures {
        let captures = g.tys(2);
        module.closure_types.push(ClosureTy {
            func: FuncTyId::new(0),
            captures,
        });
    }
    // Every node, one past each table, a few spellings around them, and
    // some random types.
    let mut types: Vec<Ty> = Vec::new();
    for id in 0..=g.structs + 1 {
        types.push(Ty::Struct(StructId::new(id)));
    }
    for id in 0..=g.enums + 1 {
        types.push(Ty::Enum(EnumId::new(id)));
    }
    for id in 0..=g.records {
        types.push(Ty::Record(RecordId::new(id)));
    }
    for id in 0..=g.closures {
        types.push(Ty::Closure(ClosureTyId::new(id)));
    }
    for id in 0..=g.types {
        types.push(Ty::Array(TyId::new(id), 1));
        types.push(Ty::Sequence(TyId::new(id)));
        types.push(Ty::Refine(TyId::new(id), PredId::new(0)));
    }
    types.push(Ty::Char);
    types.push(Ty::Vector(Box::new(Ty::Char), 4));
    types.push(Ty::Tensor(Box::new(Ty::Char), 1));
    types.push(Ty::Tensor(Box::new(Ty::Struct(StructId::new(0))), 2));
    types.push(Ty::Ref(Box::new(Ty::Char)));
    types.push(Ty::Tuple(vec![Ty::U8, Ty::Struct(StructId::new(0))]));
    types.push(Ty::PtrConst(Box::new(Ty::Struct(StructId::new(0)))));
    for _ in 0..6 {
        let ty = g.ty(2);
        types.push(ty);
    }
    (module, types)
}

#[test]
fn random_modules_judge_every_load_as_the_unbounded_old_walk_did() {
    let mut census = Census::default();
    for case in 0..3000u64 {
        let (module, types) = random_module(case.wrapping_mul(0x9e37_79b9) ^ 0xc4a7_5eed);
        compare(&format!("random {case}"), &module, &types, &mut census);
    }
    eprintln!("random modules: {census:?}");
    assert!(census.carried > 5000, "{census:?}");
    assert!(census.clean > 5000, "{census:?}");
}

// ---------------------------------------------------------------------------
// Deep shapes
// ---------------------------------------------------------------------------

fn strukt(id: u32, fields: Vec<Ty>) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: format!("S{id}"),
        fields: fields
            .into_iter()
            .map(|ty| FieldDef {
                name: "f".into(),
                ty,
                offset: None,
            })
            .collect(),
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    }
}

fn s(id: u32) -> Ty {
    Ty::Struct(StructId::new(id))
}

/// What a deep chain stands on (struct 0's one field).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Bottom {
    CharFree,
    Char,
    /// A struct id the module does not define.
    Dangling,
    /// The chain's middle: its lower half is a ring.
    Ring,
}

/// `depth` levels, level `k` holding level `k - 1` by value through the
/// `k % 8`-th wrapper: a struct field, an enum variant, a record field, a
/// closure capture, an `Array` entry, a `Sequence` entry, an inline tuple, an
/// inline vector. Level `k` is the type `level(k)` (a struct).
fn wrapped_chain(depth: u32, bottom: Bottom) -> Module {
    let mut module = Module::new("deep");
    module.func_types.push(FuncTy {
        params: vec![],
        returns: vec![],
        abi: None,
        is_vararg: false,
    });
    let floor = match bottom {
        Bottom::CharFree => Ty::U32,
        Bottom::Char => Ty::Char,
        Bottom::Dangling => s(depth + 7),
        Bottom::Ring => s(depth / 2),
    };
    module.structs.push(strukt(0, vec![Ty::U8, floor]));
    for k in 1..depth {
        let below = s(k - 1);
        let held = match k % 8 {
            0 => below,
            1 => {
                let id = EnumId::new(module.enums.len() as u32);
                module.enums.push(EnumDef::new(
                    id,
                    format!("E{k}"),
                    vec![
                        EnumVariant {
                            name: "A".into(),
                            fields: vec![Ty::U8],
                            field_names: Vec::new(),
                        },
                        EnumVariant {
                            name: "B".into(),
                            fields: vec![below],
                            field_names: Vec::new(),
                        },
                    ],
                ));
                Ty::Enum(id)
            }
            2 => {
                let id = RecordId::new(module.records.len() as u32);
                module.records.push(RecordDef {
                    id,
                    name: format!("R{k}"),
                    fields: vec![FieldDef {
                        name: "r".into(),
                        ty: below,
                        offset: None,
                    }],
                });
                Ty::Record(id)
            }
            3 => {
                let id = ClosureTyId::new(module.closure_types.len() as u32);
                module.closure_types.push(ClosureTy {
                    func: FuncTyId::new(0),
                    captures: vec![Ty::Ptr, below],
                });
                Ty::Closure(id)
            }
            4 => Ty::Array(
                module
                    .add_type(below)
                    .expect("Module::add_type: test fixture"),
                2,
            ),
            5 => Ty::Sequence(
                module
                    .add_type(below)
                    .expect("Module::add_type: test fixture"),
            ),
            6 => Ty::Tuple(vec![Ty::U16, below]),
            _ => Ty::Vector(Box::new(below), 2),
        };
        module.structs.push(strukt(k, vec![held]));
    }
    module
}

/// `P0 = { bottom }`, `P{k+1} = { Pk, Pk }`: 2^depth paths.
fn tower(depth: u32, bottom: Ty) -> Module {
    let mut module = Module::new("tower");
    module.structs.push(strukt(0, vec![bottom]));
    for k in 1..=depth {
        module.structs.push(strukt(k, vec![s(k - 1), s(k - 1)]));
    }
    module
}

/// Table rows and the type nodes they spell: what its verdicts may cost.
fn module_size(module: &Module) -> u64 {
    let rows = module.types.len()
        + module.structs.len()
        + module.enums.len()
        + module.records.len()
        + module.closure_types.len();
    u64::from(unbounded(module, &Ty::Unit)) + rows as u64
}

/// Every spelling's verdict on a load of the top, the middle and the bottom
/// of `module`, and the mirror's work linear in it.
fn judge(label: &str, module: &Module, levels: &[Ty], want: bool) {
    let summary = CharCarriers::of(module);
    assert!(
        summary.work() <= 4 * module_size(module) + 64,
        "{label}: mirror work {} over {} spelled types",
        summary.work(),
        module_size(module)
    );
    let (classifier_walk, mirror_walk) = module_walks(module, levels);
    for (index, ty) in levels.iter().enumerate() {
        let label = format!("{label}: load {ty:?}");
        assert_eq!(
            classifier_walk[index], want,
            "{label}: classifier, module walk"
        );
        assert_eq!(mirror_walk[index], want, "{label}: mirror, module walk");
        assert_eq!(summary.carries(ty), want, "{label}: mirror summary");
        assert_eq!(
            ConformanceSubset::char_origin_excluded_in(module, &load(ty.clone())).is_some(),
            want,
            "{label}: classifier, one shot"
        );
    }
}

fn deep_shapes(depth: u32) {
    for (bottom, want) in [
        (Bottom::CharFree, false),
        (Bottom::Char, true),
        (Bottom::Dangling, true),
        (Bottom::Ring, true),
    ] {
        let module = wrapped_chain(depth, bottom);
        let levels = [s(depth - 1), s(depth / 2), s(depth / 2 + 1), s(0)];
        // The bottom half of a ring is the ring; below a dangling or `Char`
        // floor every level carries; a char-free chain carries nothing.
        judge(
            &format!("{bottom:?} chain of {depth}"),
            &module,
            &levels,
            want,
        );
    }
    for (bottom, want) in [(Ty::U64, false), (Ty::Char, true)] {
        let module = tower(depth, bottom.clone());
        judge(
            &format!("tower of {depth} over {bottom:?}"),
            &module,
            &[s(depth), s(depth / 2), s(0)],
            want,
        );
    }
}

#[test]
fn deep_chains_and_towers_are_judged_whole_on_a_small_stack() {
    // The work bound and the verdicts FIRST, at a size the old walk can
    // still be asked about: past its budget it refused the char-free chain.
    deep_shapes(2000);
    let worker = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| deep_shapes(100_000))
        .expect("spawn");
    worker.join().expect("no stack overflow, linear work");
}

#[test]
fn a_char_free_type_past_the_old_budget_is_in_the_subset() {
    // Under 24 levels both walks admit a char-free chain; from 24 levels the
    // old budget refused it as "a `Char` loaded from memory".
    let mut census = Census::default();
    for depth in [2, 12, 23, 24, 25, 40, 200] {
        let module = wrapped_chain(depth, Bottom::CharFree);
        let levels: Vec<Ty> = (0..depth).map(s).collect();
        compare(
            &format!("char-free chain of {depth}"),
            &module,
            &levels,
            &mut census,
        );
        // Each level spends at least one unit of the old budget.
        let old = old_walk(&module, &s(depth - 1), OLD_BUDGET);
        if depth <= 4 {
            assert!(!old, "the old walk admitted {depth} levels");
        }
        if depth >= OLD_BUDGET {
            assert!(old, "the old walk refused {depth} levels");
        }
    }
    eprintln!("char-free chains: {census:?}");
    assert_eq!(census.carried, 0, "{census:?}");
    assert!(census.cut_off > 150, "{census:?}");
    // And a tower 40 high (2^40 paths, more than the old walk could ever
    // take) is admitted, its work one step per level.
    judge("tower of 40", &tower(40, Ty::U64), &[s(40)], false);
}
