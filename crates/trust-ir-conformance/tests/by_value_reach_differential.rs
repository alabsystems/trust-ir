// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The layout-sensitive cast rule's reachability predicates —
//! `type_reaches_handle`, `type_holds_closure_by_value`,
//! `type_stores_bool_lane`, decided once per node by `trust_ir`'s
//! reachability memo — and the rule H carrier walk (`callable_carriers`,
//! now on an all-definitions index), against the walks they replaced, kept
//! verbatim as the oracle in `by_value_reach_oracle/`.
//!
//! Every question is answered by the oracle, by the `Module` method (a fresh
//! memo per call) and by `LayoutTable`s SHARED across all of a module's
//! questions, one per query order, each asked every question twice (the
//! second pass reads the memo). The handle question is also held to the
//! whole-module summary (`NominalTypeReachability::contains_handle`), and
//! the cast rule (`layout_sensitive_cast_evidence`) to the old rule over the
//! old walks.
//!
//! * the fixture corpus (every JSON and text module under `tests/fixtures`);
//! * random type graphs: type-table entries, signatures, structs, enums,
//!   records (missing and duplicate ids) and closure types referencing each
//!   other by value, through pointers and through signatures, with handle,
//!   bool and closure seeds, cycles through every kind, on four targets;
//!   small ones (up to 8 rows a table) in bulk, and large ones (50 to 100
//!   rows) also held to a second oracle of another kind: the least fixpoint
//!   of `reach`'s table over every node of the module, by Kleene iteration,
//!   for the three predicates and the cast rule's three refusal arms;
//! * every query order of hand-built cycles (a seed behind a ring entered
//!   from every node, a ring with no seed, figure eights);
//! * the shapes the old walks could not take: 10^5-deep chains through every
//!   node kind on a 256 KiB stack (the native recursion overflowed 8 MiB),
//!   `P{k+1} = {Pk, Pk}` to 10^5 levels, and one cast per level of a 10^5-deep
//!   chain on one table, each with the memo's work counters held to a linear
//!   bound before the large run.

mod by_value_reach_oracle;

use by_value_reach_oracle as oracle;
use std::collections::BTreeMap;
use std::path::Path;
use trust_ir::ty::{
    ClosureTy, DialectTy, EnumDef, EnumVariant, FatPtrKind, FieldDef, FuncTy, HandleTy, RecordDef,
    SetRepr, StructDef, StructRepr, Ty,
};
use trust_ir::value::{ClosureTyId, EnumId, FuncTyId, PredId, RecordId, StructId, TyId};
use trust_ir::{
    CallableCarriers, CastLayoutEvidence, CastOp, Endianness, LayoutError, LayoutTable, Module,
    TargetInfo,
};

// ---------------------------------------------------------------------------
// Questions and the comparison
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
enum Query {
    Handle(Ty),
    Closure(Ty),
    BoolLane(Ty),
    Carriers(Ty),
    Cast(CastOp, Ty, Ty),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Answer {
    Holds(bool),
    Carriers(CallableCarriers),
    Cast(Result<CastLayoutEvidence, LayoutError>),
}

fn ask_oracle(module: &Module, query: &Query) -> Answer {
    match query {
        Query::Handle(ty) => Answer::Holds(oracle::type_reaches_handle(module, ty)),
        Query::Closure(ty) => Answer::Holds(oracle::type_holds_closure_by_value(module, ty)),
        Query::BoolLane(ty) => Answer::Holds(oracle::type_stores_bool_lane(module, ty)),
        Query::Carriers(ty) => Answer::Carriers(oracle::callable_carriers(module, ty)),
        Query::Cast(op, src, dst) => Answer::Cast(oracle::layout_sensitive_cast_evidence(
            module, *op, src, dst,
        )),
    }
}

fn ask_module(module: &Module, query: &Query) -> Answer {
    match query {
        Query::Handle(ty) => Answer::Holds(module.type_reaches_handle(ty)),
        Query::Closure(ty) => Answer::Holds(module.type_holds_closure_by_value(ty)),
        Query::BoolLane(ty) => Answer::Holds(module.type_stores_bool_lane(ty)),
        Query::Carriers(ty) => Answer::Carriers(module.callable_carriers(ty)),
        Query::Cast(op, src, dst) => {
            Answer::Cast(module.layout_sensitive_cast_evidence(*op, src, dst))
        }
    }
}

fn ask_table(table: &LayoutTable<'_>, query: &Query) -> Answer {
    match query {
        Query::Handle(ty) => Answer::Holds(table.type_reaches_handle(ty)),
        Query::Closure(ty) => Answer::Holds(table.type_holds_closure_by_value(ty)),
        Query::BoolLane(ty) => Answer::Holds(table.type_stores_bool_lane(ty)),
        // Not a table question: the carrier census is a set per value.
        Query::Carriers(ty) => Answer::Carriers(table.module().callable_carriers(ty)),
        Query::Cast(op, src, dst) => {
            Answer::Cast(table.layout_sensitive_cast_evidence(*op, src, dst))
        }
    }
}

/// What a comparison run saw, so a vacuous run fails.
#[derive(Default, Debug)]
struct Census {
    modules: usize,
    queries: usize,
    /// Per predicate: (yes, no).
    holds: BTreeMap<&'static str, (usize, usize)>,
    carriers_nonempty: usize,
    carriers_opaque: usize,
    casts: BTreeMap<&'static str, usize>,
}

fn predicate_name(query: &Query) -> &'static str {
    match query {
        Query::Handle(_) => "handle",
        Query::Closure(_) => "closure",
        Query::BoolLane(_) => "bool-lane",
        Query::Carriers(_) => "carriers",
        Query::Cast(..) => "cast",
    }
}

fn cast_name(answer: &Result<CastLayoutEvidence, LayoutError>) -> &'static str {
    match answer {
        Ok(CastLayoutEvidence::NotLayoutSensitive) => "NotLayoutSensitive",
        Ok(CastLayoutEvidence::SameSize { .. }) => "SameSize",
        Ok(CastLayoutEvidence::PointerCast { .. }) => "PointerCast",
        Ok(CastLayoutEvidence::ReifyFnPointer { .. }) => "ReifyFnPointer",
        Err(LayoutError::OpaqueHandleCast { .. }) => "OpaqueHandleCast",
        Err(LayoutError::ClosureCast { .. }) => "ClosureCast",
        Err(LayoutError::BoolLaneReinterpret { .. }) => "BoolLaneReinterpret",
        Err(LayoutError::CastSizeMismatch { .. }) => "CastSizeMismatch",
        Err(_) => "other-refusal",
    }
}

/// Every question, answered by the oracle, by the `Module` methods, and by
/// one table per order in `orders`, shared across the module's questions and
/// asked every question twice in that order, must agree; a handle question
/// also with the whole-module summary.
fn compare(
    label: &str,
    module: &Module,
    queries: &[Query],
    orders: &[Vec<usize>],
    census: &mut Census,
) {
    let want: Vec<Answer> = queries.iter().map(|q| ask_oracle(module, q)).collect();
    let summary = module.nominal_type_reachability();
    for (query, want) in queries.iter().zip(&want) {
        let got = ask_module(module, query);
        assert_eq!(&got, want, "{label}: Module answer for {query:?}");
        if let Query::Handle(ty) = query {
            assert_eq!(
                Answer::Holds(summary.contains_handle(ty)),
                *want,
                "{label}: whole-module summary for {query:?}"
            );
        }
    }
    for (number, order) in orders.iter().enumerate() {
        let shared = LayoutTable::new(module);
        for pass in 0..2 {
            for &index in order {
                let got = ask_table(&shared, &queries[index]);
                assert_eq!(
                    got, want[index],
                    "{label}: shared table {number}, pass {pass}, for {:?}",
                    queries[index]
                );
            }
        }
    }
    census.modules += 1;
    census.queries += queries.len();
    for (query, answer) in queries.iter().zip(&want) {
        match answer {
            Answer::Holds(holds) => {
                let entry = census.holds.entry(predicate_name(query)).or_default();
                if *holds {
                    entry.0 += 1;
                } else {
                    entry.1 += 1;
                }
            }
            Answer::Carriers(carriers) => {
                census.carriers_nonempty += usize::from(carriers.carries_typed_callable());
                census.carriers_opaque += usize::from(carriers.opaque);
            }
            Answer::Cast(cast) => *census.casts.entry(cast_name(cast)).or_default() += 1,
        }
    }
}

/// `count` shuffled orders of `n` queries, then the first one reversed.
fn orders(rng: &mut Rng, n: usize, count: usize) -> Vec<Vec<usize>> {
    let mut orders: Vec<Vec<usize>> = (0..count).map(|_| rng.permutation(n)).collect();
    if let Some(first) = orders.first() {
        orders.push(first.iter().rev().copied().collect());
    }
    orders
}

/// The four reachability questions of one type.
fn ask_all(queries: &mut Vec<Query>, ty: Ty) {
    queries.push(Query::Handle(ty.clone()));
    queries.push(Query::Closure(ty.clone()));
    queries.push(Query::BoolLane(ty.clone()));
    queries.push(Query::Carriers(ty));
}

/// The questions a module invites: every nominal id it defines and one it
/// does not, every type-table entry inline and through `Array` / `Refine`
/// (and one past the end), every signature and closure type (and one absent),
/// every field, variant field, capture and signature type as written, a few
/// wrappers (a pointer, a vector, a tensor, a tuple), and casts between `casts` pairs
/// of them under every layout-sensitive operation and one that is not.
fn module_queries(module: &Module, rng: &mut Rng, casts: usize) -> Vec<Query> {
    let mut types: Vec<Ty> = Vec::new();
    let ids = |present: Vec<u32>| {
        let mut ids = present;
        ids.sort_unstable();
        ids.dedup();
        let absent = ids.last().map_or(Some(0), |id| id.checked_add(1));
        ids.into_iter().chain(absent).collect::<Vec<u32>>()
    };
    for id in ids(module.structs.iter().map(|def| def.id.index()).collect()) {
        types.push(Ty::Struct(StructId::new(id)));
    }
    for id in ids(module.enums.iter().map(|def| def.id.index()).collect()) {
        types.push(Ty::Enum(EnumId::new(id)));
    }
    for id in ids(module.records.iter().map(|def| def.id.index()).collect()) {
        types.push(Ty::Record(RecordId::new(id)));
    }
    for index in 0..=module.types.len() {
        let id = TyId::new(index as u32);
        if let Some(ty) = module.types.get(index) {
            types.push(ty.clone());
        }
        types.push(Ty::Array(id, 2));
        types.push(Ty::Array(id, 0));
        types.push(Ty::Refine(id, PredId::new(0)));
        types.push(Ty::Sequence(id));
    }
    for index in 0..=module.func_types.len() {
        types.push(Ty::Func(FuncTyId::new(index as u32)));
    }
    for index in 0..=module.closure_types.len() {
        types.push(Ty::Closure(ClosureTyId::new(index as u32)));
    }
    let mut written: Vec<&Ty> = Vec::new();
    written.extend(
        module
            .structs
            .iter()
            .flat_map(|def| def.fields.iter().map(|f| &f.ty)),
    );
    written.extend(
        module
            .records
            .iter()
            .flat_map(|def| def.fields.iter().map(|f| &f.ty)),
    );
    written.extend(
        module
            .enums
            .iter()
            .flat_map(|def| def.variants.iter().flat_map(|v| v.fields.iter())),
    );
    written.extend(module.closure_types.iter().flat_map(|c| c.captures.iter()));
    written.extend(
        module
            .func_types
            .iter()
            .flat_map(|f| f.params.iter().chain(&f.returns)),
    );
    let mut seen = std::collections::BTreeSet::new();
    for ty in written {
        if seen.insert(format!("{ty:?}")) {
            types.push(ty.clone());
        }
    }
    let wrappers: Vec<Ty> = types
        .iter()
        .take(6)
        .flat_map(|ty| {
            [
                Ty::Ref(Box::new(ty.clone())),
                Ty::Vector(Box::new(ty.clone()), 2),
                Ty::Tensor(Box::new(ty.clone()), 1),
                Ty::Tuple(vec![Ty::U8, ty.clone()]),
            ]
        })
        .collect();
    types.extend(wrappers);
    types.push(Ty::Tuple(Vec::new()));
    types.push(Ty::Bool);
    types.push(Ty::Ptr);

    let mut queries = Vec::new();
    for ty in &types {
        ask_all(&mut queries, ty.clone());
    }
    let ops = [
        CastOp::Bitcast,
        CastOp::Transmute,
        CastOp::PtrToPtr,
        CastOp::ReifyFnPointer,
        CastOp::Trunc,
    ];
    let pick = |rng: &mut Rng, types: &[Ty]| match rng.below(8) {
        0 => Ty::U64,
        1 => Ty::Ptr,
        _ => types[rng.below(types.len() as u64) as usize].clone(),
    };
    for _ in 0..casts {
        let src = pick(rng, &types);
        let dst = if rng.chance(15) {
            src.clone()
        } else {
            pick(rng, &types)
        };
        let op = ops[rng.below(ops.len() as u64) as usize];
        queries.push(Query::Cast(op, src, dst));
    }
    queries
}

// ---------------------------------------------------------------------------
// The fixture corpus
// ---------------------------------------------------------------------------

fn corpus_modules() -> Vec<(String, Module)> {
    let mut modules = Vec::new();
    let mut stack = vec![
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests")
            .join("fixtures"),
    ];
    let mut files = Vec::new();
    while let Some(dir) = stack.pop() {
        for entry in std::fs::read_dir(&dir).expect("read fixtures dir") {
            let path = entry.expect("fixture entry").path();
            if path.is_dir() {
                stack.push(path);
            } else {
                files.push(path);
            }
        }
    }
    files.sort();
    for path in files {
        let name = path.display().to_string();
        let module = match path.extension().and_then(|ext| ext.to_str()) {
            Some("json") => std::fs::read(&path)
                .ok()
                .and_then(|bytes| serde_json::from_slice::<Module>(&bytes).ok()),
            Some("trust_ir") => std::fs::read_to_string(&path)
                .ok()
                .and_then(|text| trust_ir::parser::parse_module(&text).ok()),
            _ => None,
        };
        if let Some(module) = module {
            modules.push((name, module));
        }
    }
    modules
}

#[test]
fn the_fixture_corpus_answers_exactly_as_the_old_walks_did() {
    let mut census = Census::default();
    let mut rng = Rng(0x0b1_7a1e);
    for (name, module) in corpus_modules() {
        let queries = module_queries(&module, &mut rng, 64);
        let orders = orders(&mut rng, queries.len(), 1);
        compare(&name, &module, &queries, &orders, &mut census);
    }
    eprintln!("fixture corpus: {census:?}");
    assert!(census.modules >= 100, "{census:?}");
    // Not vacuous: the corpus holds a handle, a closure and a bool lane.
    for predicate in ["handle", "closure", "bool-lane"] {
        let (yes, no) = census.holds.get(predicate).copied().unwrap_or_default();
        assert!(yes > 0 && no > 0, "{predicate}: {census:?}");
    }
}

// ---------------------------------------------------------------------------
// Random type graphs
// ---------------------------------------------------------------------------

/// splitmix64: deterministic, dependency-free.
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

    fn permutation(&mut self, n: usize) -> Vec<usize> {
        let mut order: Vec<usize> = (0..n).collect();
        for i in (1..n).rev() {
            let j = self.below(i as u64 + 1) as usize;
            order.swap(i, j);
        }
        order
    }
}

/// A random type over a module with these table sizes (ids may run one past
/// the end, so some references are missing).
struct Gen {
    rng: Rng,
    types: u32,
    func_types: u32,
    structs: u32,
    enums: u32,
    records: u32,
    closures: u32,
    /// Percent of leaves that are a seed (handle, closure or bool).
    seeds: u64,
    /// Added to every list's maximum length: denser graphs, longer paths.
    more: u64,
}

impl Gen {
    fn id(&mut self, n: u32) -> u32 {
        self.rng.below(u64::from(n) + 1) as u32
    }

    fn leaf(&mut self) -> Ty {
        if self.rng.chance(self.seeds) {
            return match self.rng.below(3) {
                0 => Ty::Handle(Box::new(HandleTy::new("Nat", "trust_bignum::Nat"))),
                1 => Ty::Closure(ClosureTyId::new(self.id(self.closures))),
                _ => Ty::Bool,
            };
        }
        match self.rng.below(16) {
            0 => Ty::U8,
            1 => Ty::U64,
            2 => Ty::I32,
            3 => Ty::Unit,
            4 => Ty::Never,
            5 => Ty::Ptr,
            6 => Ty::Func(FuncTyId::new(self.id(self.func_types))),
            7 => Ty::FatPtr(FatPtrKind::Slice(TyId::new(self.id(self.types)))),
            8 => Ty::FatPtr(FatPtrKind::Str),
            9 => Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 3 }),
            10 => Ty::FatPtr(FatPtrKind::ContainerVtable),
            11 => Ty::Set(TyId::new(self.id(self.types)), SetRepr::Bitset),
            12 => Ty::Sequence(TyId::new(self.id(self.types))),
            13 => Ty::Dialect(Box::new(DialectTy::new("example", "value", 1))),
            14 => Ty::Error,
            _ => Ty::Char,
        }
    }

    fn ty(&mut self, depth: u32) -> Ty {
        match self.rng.below(100) {
            0..=29 => self.leaf(),
            30..=42 => Ty::Struct(StructId::new(self.id(self.structs))),
            43..=52 => Ty::Enum(EnumId::new(self.id(self.enums))),
            53..=59 => Ty::Record(RecordId::new(self.id(self.records))),
            60..=67 => {
                let len = self.rng.below(3);
                Ty::Array(TyId::new(self.id(self.types)), len)
            }
            68..=72 => Ty::Refine(TyId::new(self.id(self.types)), PredId::new(0)),
            73..=80 if depth > 0 => {
                let inner = Box::new(self.ty(depth - 1));
                match self.rng.below(5) {
                    0 => Ty::Ref(inner),
                    1 => Ty::RefMut(inner),
                    2 => Ty::PtrConst(inner),
                    3 => Ty::PtrMut(inner),
                    _ => Ty::Rc(inner),
                }
            }
            81..=88 if depth > 0 => Ty::Vector(Box::new(self.ty(depth - 1)), 2),
            89..=99 if depth > 0 => {
                let n = self.rng.below(4);
                Ty::Tuple((0..n).map(|_| self.ty(depth - 1)).collect())
            }
            _ => self.leaf(),
        }
    }

    fn tys(&mut self, max: u64) -> Vec<Ty> {
        let n = self.rng.below(max + self.more + 1);
        (0..n).map(|_| self.ty(2)).collect()
    }
}

fn target(rng: &mut Rng) -> Option<TargetInfo> {
    let (triple, pointer_size) = match rng.below(10) {
        0..=1 => return None,
        2..=6 => ("x86_64-unknown-linux-gnu", 8),
        7 => ("aarch64-apple-darwin", 8),
        8 => ("wasm32-unknown-unknown", 4),
        _ => ("i686-unknown-linux-gnu", 4),
    };
    Some(TargetInfo {
        triple: triple.into(),
        pointer_size,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    })
}

fn field(index: usize, ty: Ty) -> FieldDef {
    FieldDef {
        name: format!("f{index}"),
        ty,
        offset: Some(8 * index as u64),
    }
}

/// A random module: every table references the others by id, by value,
/// through pointers and through signatures; ids collide (duplicates) and run
/// past the end (missing). The type and struct tables have `min` to
/// `min + span - 1` rows; the others grow with them past 8 rows, and the
/// seeds thin out so that a large graph is not all "yes".
fn random_module(seed: u64, min: u32, span: u64) -> Module {
    let mut rng = Rng(seed);
    let size = min + rng.below(span) as u32;
    let extra = u64::from(size.saturating_sub(8) / 4);
    let mut g = Gen {
        rng: Rng(seed ^ 0x5eed),
        types: size,
        func_types: 1 + rng.below(3 + extra) as u32,
        structs: size,
        enums: 1 + rng.below(u64::from(size)) as u32,
        records: rng.below(4 + extra) as u32,
        closures: rng.below(4 + extra) as u32,
        seeds: if extra == 0 {
            [0, 4, 10, 25][rng.below(4) as usize]
        } else {
            [2, 5, 10, 20][rng.below(4) as usize]
        },
        more: extra.min(3),
    };
    let mut module = Module::new("reach");
    module.target_info = target(&mut rng);
    for _ in 0..g.types {
        let ty = g.ty(2);
        module.types.push(ty);
    }
    for _ in 0..g.func_types {
        let params = g.tys(2);
        let returns = g.tys(1);
        module.func_types.push(FuncTy {
            params,
            returns,
            abi: None,
            is_vararg: false,
        });
    }
    for index in 0..g.structs {
        // A duplicate id now and then: every definition counts.
        let id = if index > 0 && g.rng.chance(10) {
            g.rng.below(u64::from(index)) as u32
        } else {
            index
        };
        let fields: Vec<FieldDef> = g
            .tys(3)
            .into_iter()
            .enumerate()
            .map(|(i, ty)| field(i, ty))
            .collect();
        let size = 8 * fields.len() as u64;
        module.structs.push(StructDef {
            id: StructId::new(id),
            name: format!("S{index}"),
            fields,
            size: Some(size),
            align: Some(8),
            repr: StructRepr::C,
            origin: None,
        });
    }
    for index in 0..g.enums {
        let id = if index > 0 && g.rng.chance(10) {
            g.rng.below(u64::from(index)) as u32
        } else {
            index
        };
        let variants = (0..g.rng.below(3) + 1)
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
        let id = if index > 0 && g.rng.chance(15) {
            g.rng.below(u64::from(index)) as u32
        } else {
            index
        };
        let fields = g
            .tys(2)
            .into_iter()
            .enumerate()
            .map(|(i, ty)| FieldDef {
                name: format!("r{i}"),
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
        let func = FuncTyId::new(g.id(g.func_types));
        let captures = g.tys(2);
        module.closure_types.push(ClosureTy { func, captures });
    }
    module
}

#[test]
fn random_type_graphs_answer_exactly_as_the_old_walks_did() {
    let mut census = Census::default();
    let mut rng = Rng(0x7ea_c4ab1e);
    for case in 0..6000u64 {
        let module = random_module(case.wrapping_mul(0x9e37_79b9) ^ 0xbad_5eed, 1, 8);
        let queries = module_queries(&module, &mut rng, 24);
        let orders = orders(&mut rng, queries.len(), 2);
        compare(
            &format!("random {case}"),
            &module,
            &queries,
            &orders,
            &mut census,
        );
    }
    eprintln!("random graphs: {census:?}");
    for predicate in ["handle", "closure", "bool-lane"] {
        let (yes, no) = census.holds.get(predicate).copied().unwrap_or_default();
        assert!(yes > 1000 && no > 1000, "{predicate}: {census:?}");
    }
    assert!(census.carriers_nonempty > 1000, "{census:?}");
    assert!(census.carriers_opaque > 1000, "{census:?}");
    // Every arm of the cast rule the predicates guard is reached.
    for verdict in [
        "NotLayoutSensitive",
        "SameSize",
        "PointerCast",
        "ReifyFnPointer",
        "OpaqueHandleCast",
        "ClosureCast",
        "BoolLaneReinterpret",
        "CastSizeMismatch",
    ] {
        assert!(
            census.casts.get(verdict).copied().unwrap_or(0) > 0,
            "{verdict}: {census:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// Large random graphs, and a second oracle: a whole-module fixpoint
// ---------------------------------------------------------------------------

/// The three predicates decided another way than the old walks: as the
/// least fixpoint of the reachability table in `trust_ir::reach`'s module
/// docs, by Kleene iteration over EVERY node of the module (and one past the
/// end of each table), with no walk, no visited set and no memo shared with
/// a query.
mod fixpoint {
    use std::collections::{BTreeSet, HashMap};

    use trust_ir::Module;
    use trust_ir::ty::{FatPtrKind, Ty};

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
    enum Node {
        Ty(usize),
        Func(usize),
        Struct(u32),
        Enum(u32),
        Record(u32),
        Closure(usize),
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum Predicate {
        Handle,
        Closure,
        Bool,
    }

    const PREDICATES: [Predicate; 3] = [Predicate::Handle, Predicate::Closure, Predicate::Bool];

    /// `true` when `ty` holds a seed of `p` inline; pushes the nodes its
    /// inline children name.
    fn inline(p: Predicate, ty: &Ty, out: &mut Vec<Node>) -> bool {
        let mut seeded = false;
        match ty {
            Ty::Handle(_) => seeded = p == Predicate::Handle,
            Ty::Closure(id) => match p {
                Predicate::Closure => seeded = true,
                Predicate::Handle => out.push(Node::Closure(id.as_usize())),
                Predicate::Bool => {}
            },
            Ty::Bool => seeded = p == Predicate::Bool,
            Ty::Tuple(elems) => {
                for elem in elems {
                    seeded |= inline(p, elem, out);
                }
            }
            // A tensor's element is inline, as a vector's lane is.
            Ty::Vector(elem, _) | Ty::Tensor(elem, _) => seeded = inline(p, elem, out),
            Ty::Ref(inner)
            | Ty::RefMut(inner)
            | Ty::PtrConst(inner)
            | Ty::PtrMut(inner)
            | Ty::Rc(inner) => {
                // Only the handle question looks behind an address.
                if p == Predicate::Handle {
                    seeded = inline(p, inner, out);
                }
            }
            Ty::Array(id, _) | Ty::Refine(id, _) => out.push(Node::Ty(id.as_usize())),
            Ty::Set(id, _) | Ty::Sequence(id) | Ty::FatPtr(FatPtrKind::Slice(id)) => {
                if p == Predicate::Handle {
                    out.push(Node::Ty(id.as_usize()));
                }
            }
            Ty::Func(id) => {
                if p == Predicate::Handle {
                    out.push(Node::Func(id.as_usize()));
                }
            }
            Ty::Struct(id) => out.push(Node::Struct(id.index())),
            Ty::Enum(id) => out.push(Node::Enum(id.index())),
            Ty::Record(id) if p != Predicate::Bool => out.push(Node::Record(id.index())),
            _ => {}
        }
        seeded
    }

    /// `true` when a member type of `node` holds a seed inline; pushes the
    /// nodes its member types name.
    fn members(module: &Module, p: Predicate, node: Node, out: &mut Vec<Node>) -> bool {
        let mut seeded = false;
        let mut each = |ty: &Ty, out: &mut Vec<Node>| seeded |= inline(p, ty, out);
        match node {
            Node::Ty(index) => {
                if let Some(ty) = module.types.get(index) {
                    each(ty, out);
                }
            }
            Node::Func(index) => {
                if let Some(signature) = module.func_types.get(index) {
                    signature
                        .params
                        .iter()
                        .chain(&signature.returns)
                        .for_each(|ty| each(ty, out));
                }
            }
            Node::Struct(id) => {
                for def in module.structs.iter().filter(|def| def.id.index() == id) {
                    def.fields.iter().for_each(|field| each(&field.ty, out));
                }
            }
            Node::Enum(id) => {
                for def in module.enums.iter().filter(|def| def.id.index() == id) {
                    def.variants
                        .iter()
                        .flat_map(|variant| &variant.fields)
                        .for_each(|ty| each(ty, out));
                }
            }
            Node::Record(id) => {
                for def in module.records.iter().filter(|def| def.id.index() == id) {
                    def.fields.iter().for_each(|field| each(&field.ty, out));
                }
            }
            Node::Closure(index) => {
                if let Some(closure) = module.closure_types.get(index) {
                    closure.captures.iter().for_each(|ty| each(ty, out));
                    out.push(Node::Func(closure.func.as_usize()));
                }
            }
        }
        seeded
    }

    /// Every node's verdict for each predicate.
    pub struct Fixpoint {
        holds: [HashMap<Node, bool>; 3],
    }

    impl Fixpoint {
        pub fn new(module: &Module) -> Self {
            let mut universe: BTreeSet<Node> = BTreeSet::new();
            universe.extend((0..=module.types.len()).map(Node::Ty));
            universe.extend((0..=module.func_types.len()).map(Node::Func));
            universe.extend((0..=module.closure_types.len()).map(Node::Closure));
            for def in &module.structs {
                universe.insert(Node::Struct(def.id.index()));
            }
            for def in &module.enums {
                universe.insert(Node::Enum(def.id.index()));
            }
            for def in &module.records {
                universe.insert(Node::Record(def.id.index()));
            }
            let mut holds: [HashMap<Node, bool>; 3] = Default::default();
            for (k, p) in PREDICATES.into_iter().enumerate() {
                let rows: Vec<(Node, bool, Vec<Node>)> = universe
                    .iter()
                    .map(|&node| {
                        let mut out = Vec::new();
                        let seeded = members(module, p, node, &mut out);
                        (node, seeded, out)
                    })
                    .collect();
                let mut value: HashMap<Node, bool> = rows
                    .iter()
                    .map(|(node, seeded, _)| (*node, *seeded))
                    .collect();
                loop {
                    let mut changed = false;
                    for (node, _, out) in &rows {
                        if !value[node] && out.iter().any(|m| value.get(m) == Some(&true)) {
                            value.insert(*node, true);
                            changed = true;
                        }
                    }
                    if !changed {
                        break;
                    }
                }
                holds[k] = value;
            }
            Fixpoint { holds }
        }

        pub fn holds(&self, p: Predicate, ty: &Ty) -> bool {
            let k = PREDICATES
                .iter()
                .position(|q| *q == p)
                .expect("a predicate");
            let mut out = Vec::new();
            // A node outside the universe is a missing id: no members.
            inline(p, ty, &mut out)
                || out
                    .iter()
                    .any(|node| self.holds[k].get(node) == Some(&true))
        }
    }
}

/// The fixpoint's answer to every predicate question, and the cast rule's
/// three refusal arms as the fixpoint decides them: a handle on either side
/// first, then a closure by value, then (a reinterpret between different
/// types) a bool lane; a cast none of them reaches is refused by none of
/// those arms.
fn compare_with_fixpoint(label: &str, module: &Module, queries: &[Query], census: &mut Census) {
    use fixpoint::Predicate;
    let fix = fixpoint::Fixpoint::new(module);
    let table = LayoutTable::new(module);
    for query in queries {
        match query {
            Query::Handle(ty) | Query::Closure(ty) | Query::BoolLane(ty) => {
                let (p, got) = match query {
                    Query::Handle(_) => (Predicate::Handle, table.type_reaches_handle(ty)),
                    Query::Closure(_) => {
                        (Predicate::Closure, table.type_holds_closure_by_value(ty))
                    }
                    _ => (Predicate::Bool, table.type_stores_bool_lane(ty)),
                };
                assert_eq!(got, fix.holds(p, ty), "{label}: fixpoint for {query:?}");
            }
            Query::Cast(op, src, dst) => {
                let got = table.layout_sensitive_cast_evidence(*op, src, dst);
                let either = |p| fix.holds(p, src) || fix.holds(p, dst);
                let arm = if !op.is_layout_sensitive() {
                    None
                } else if either(Predicate::Handle) {
                    Some("OpaqueHandleCast")
                } else if either(Predicate::Closure) {
                    Some("ClosureCast")
                } else if matches!(op, CastOp::Bitcast | CastOp::Transmute)
                    && src != dst
                    && either(Predicate::Bool)
                {
                    Some("BoolLaneReinterpret")
                } else {
                    None
                };
                let name = cast_name(&got);
                match arm {
                    Some(arm) => assert_eq!(name, arm, "{label}: fixpoint arm for {query:?}"),
                    None => assert!(
                        !matches!(
                            name,
                            "OpaqueHandleCast" | "ClosureCast" | "BoolLaneReinterpret"
                        ),
                        "{label}: {query:?} refused as {name}, which the fixpoint does not reach"
                    ),
                }
                *census.casts.entry(name).or_default() += 1;
            }
            Query::Carriers(_) => {}
        }
    }
}

#[test]
fn large_random_type_graphs_answer_as_the_old_walks_and_the_fixpoint_do() {
    let mut census = Census::default();
    let mut fixpoint_census = Census::default();
    let mut rng = Rng(0x01a7_9ec4_ab1e);
    for case in 0..160u64 {
        let module = random_module(case.wrapping_mul(0x9e37_79b9) ^ 0x1a29e, 50, 51);
        let mut queries = module_queries(&module, &mut rng, 400);
        // A sample of a large module's questions, its casts kept.
        let order = rng.permutation(queries.len());
        let mut sampled: Vec<Query> = Vec::new();
        for index in order {
            let query = &queries[index];
            if matches!(query, Query::Cast(..)) || sampled.len() < 900 {
                sampled.push(query.clone());
            }
        }
        queries = sampled;
        let orders = orders(&mut rng, queries.len(), 1);
        let label = format!("large {case}");
        compare(&label, &module, &queries, &orders, &mut census);
        compare_with_fixpoint(&label, &module, &queries, &mut fixpoint_census);
    }
    eprintln!("large random graphs: {census:?}");
    for predicate in ["handle", "closure", "bool-lane"] {
        let (yes, no) = census.holds.get(predicate).copied().unwrap_or_default();
        assert!(yes > 500 && no > 500, "{predicate}: {census:?}");
    }
    for verdict in [
        "OpaqueHandleCast",
        "ClosureCast",
        "BoolLaneReinterpret",
        "SameSize",
        "CastSizeMismatch",
    ] {
        assert!(
            fixpoint_census.casts.get(verdict).copied().unwrap_or(0) > 0,
            "{verdict}: {fixpoint_census:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// Cycles, from every entry point and in every order
// ---------------------------------------------------------------------------

fn s(id: u32) -> Ty {
    Ty::Struct(StructId::new(id))
}

fn strukt(id: u32, fields: Vec<Ty>) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: format!("S{id}"),
        size: Some(8 * fields.len() as u64),
        fields: fields
            .into_iter()
            .enumerate()
            .map(|(i, ty)| field(i, ty))
            .collect(),
        align: Some(8),
        repr: StructRepr::C,
        origin: None,
    }
}

fn handle() -> Ty {
    Ty::Handle(Box::new(HandleTy::new("Nat", "trust_bignum::Nat")))
}

/// Every order of `queries` (up to 6! = 720), each on its own shared table.
fn every_order(label: &str, module: &Module, queries: &[Query]) {
    let mut census = Census::default();
    let mut order: Vec<usize> = (0..queries.len()).collect();
    permute(&mut order, 0, &mut |order| {
        compare(label, module, queries, &[order.to_vec()], &mut census);
    });
}

fn permute(order: &mut Vec<usize>, k: usize, visit: &mut dyn FnMut(&[usize])) {
    if k == order.len() {
        visit(order);
        return;
    }
    for i in k..order.len() {
        order.swap(k, i);
        permute(order, k + 1, visit);
        order.swap(k, i);
    }
}

#[test]
fn a_cycle_answers_from_every_entry_point_as_the_old_walks_did() {
    let ring_questions = |n: u32| -> Vec<Query> {
        (0..n)
            .flat_map(|k| {
                [
                    Query::Handle(s(k)),
                    Query::Closure(s(k)),
                    Query::BoolLane(s(k)),
                ]
            })
            .collect()
    };
    // A four-ring whose third node holds each seed beside its ring edge:
    // every node reaches all three, whichever is asked first.
    let mut seeded = Module::new("seeded-ring");
    for k in 0..4 {
        let mut fields = vec![s((k + 1) % 4)];
        if k == 2 {
            fields.extend([
                handle(),
                Ty::Tuple(vec![Ty::Closure(ClosureTyId::new(0))]),
                Ty::Vector(Box::new(Ty::Bool), 4),
            ]);
        }
        seeded.structs.push(strukt(k, fields));
    }
    every_order("seeded-ring", &seeded, &ring_questions(2));
    let queries = ring_questions(4);
    let mut census = Census::default();
    let mut rng = Rng(0xc1c1e);
    let ring_orders = orders(&mut rng, queries.len(), 24);
    compare("seeded-ring", &seeded, &queries, &ring_orders, &mut census);
    assert_eq!(census.holds["handle"], (4, 0), "{census:?}");

    // The same ring with no seed: nothing reaches one.
    let mut empty = Module::new("empty-ring");
    for k in 0..4 {
        empty.structs.push(strukt(k, vec![s((k + 1) % 4), Ty::U8]));
    }
    every_order("empty-ring", &empty, &ring_questions(2));

    // A figure eight through a struct, an enum, a record and a type entry,
    // with the seeds behind pointers (followed by the handle walk only) and
    // behind a record (followed by the closure walk, never the bool walk).
    let mut eight = Module::new("figure-eight");
    eight.types.push(Ty::Array(TyId::new(0), 1)); // ty.0 = [ty.0; 1]
    eight.types.push(s(0)); // ty.1 = S0
    eight.structs.push(strukt(
        0,
        vec![
            Ty::Enum(EnumId::new(0)),
            Ty::Ref(Box::new(handle())),
            Ty::Array(TyId::new(1), 2),
        ],
    ));
    eight.enums.push(EnumDef::new(
        EnumId::new(0),
        "E0",
        vec![EnumVariant {
            name: "V".into(),
            fields: vec![s(0), Ty::Record(RecordId::new(0))],
            field_names: Vec::new(),
        }],
    ));
    eight.records.push(RecordDef {
        id: RecordId::new(0),
        name: "R0".into(),
        fields: vec![
            FieldDef {
                name: "c".into(),
                ty: Ty::Closure(ClosureTyId::new(0)),
                offset: None,
            },
            FieldDef {
                name: "b".into(),
                ty: Ty::Bool,
                offset: None,
            },
            FieldDef {
                name: "e".into(),
                ty: Ty::Enum(EnumId::new(0)),
                offset: None,
            },
        ],
    });
    let queries: Vec<Query> = [
        s(0),
        Ty::Enum(EnumId::new(0)),
        Ty::Record(RecordId::new(0)),
        Ty::Refine(TyId::new(1), PredId::new(0)),
        Ty::Array(TyId::new(0), 3),
    ]
    .into_iter()
    .flat_map(|ty| {
        [
            Query::Handle(ty.clone()),
            Query::Closure(ty.clone()),
            Query::BoolLane(ty),
        ]
    })
    .collect();
    let mut census = Census::default();
    let eight_orders = orders(&mut rng, queries.len(), 48);
    compare("figure-eight", &eight, &queries, &eight_orders, &mut census);
    // Handle: S0, E0, R0 (through E0) and ty.1 reach it; ty.0 does not.
    assert_eq!(census.holds["handle"], (4, 1), "{census:?}");
    // Closure: through the record, from every node but ty.0.
    assert_eq!(census.holds["closure"], (4, 1), "{census:?}");
    // Bool: only the record holds one, and the bool walk never enters it.
    assert_eq!(census.holds["bool-lane"], (0, 5), "{census:?}");
}

// ---------------------------------------------------------------------------
// Deep chains and shared sub-types: linear work, no recursion
// ---------------------------------------------------------------------------

/// Chains of `depth` levels through every node kind, the seed at the bottom
/// when `seeded`: structs, enums, records, type-table entries (by `Array`),
/// signatures (a parameter of the previous signature) and closure types (a
/// capture of the previous closure).
fn chains(depth: u32, seeded: bool) -> Module {
    let mut module = Module::new("chains");
    module.target_info = Some(TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    // Unseeded, every level is one word, so the casts below reach the
    // layouts.
    let all_seeds = if seeded {
        Ty::Tuple(vec![handle(), Ty::Closure(ClosureTyId::new(0)), Ty::Bool])
    } else {
        Ty::U64
    };
    let bottom = |seed: Ty| if seeded { seed } else { Ty::U64 };
    module.structs.push(strukt(
        0,
        match &all_seeds {
            Ty::Tuple(seeds) => seeds.clone(),
            word => vec![word.clone()],
        },
    ));
    module.enums.push(EnumDef::new(
        EnumId::new(0),
        "E0",
        vec![EnumVariant {
            name: "V".into(),
            fields: vec![all_seeds.clone()],
            field_names: Vec::new(),
        }],
    ));
    module.records.push(RecordDef {
        id: RecordId::new(0),
        name: "R0".into(),
        fields: vec![FieldDef {
            name: "f".into(),
            ty: all_seeds.clone(),
            offset: None,
        }],
    });
    module.types.push(all_seeds.clone());
    module.func_types.push(FuncTy {
        params: vec![bottom(handle())],
        returns: Vec::new(),
        abi: None,
        is_vararg: false,
    });
    module.closure_types.push(ClosureTy {
        func: FuncTyId::new(0),
        captures: vec![Ty::U8],
    });
    for k in 1..depth {
        module.structs.push(strukt(k, vec![s(k - 1)]));
        module.enums.push(EnumDef::new(
            EnumId::new(k),
            format!("E{k}"),
            vec![EnumVariant {
                name: "V".into(),
                fields: vec![Ty::Enum(EnumId::new(k - 1))],
                field_names: Vec::new(),
            }],
        ));
        module.records.push(RecordDef {
            id: RecordId::new(k),
            name: format!("R{k}"),
            fields: vec![FieldDef {
                name: "f".into(),
                ty: Ty::Record(RecordId::new(k - 1)),
                offset: None,
            }],
        });
        module.types.push(Ty::Array(TyId::new(k - 1), 1));
        module.func_types.push(FuncTy {
            params: vec![Ty::Func(FuncTyId::new(k - 1))],
            returns: Vec::new(),
            abi: None,
            is_vararg: false,
        });
        module.closure_types.push(ClosureTy {
            func: FuncTyId::new(0),
            captures: vec![Ty::Closure(ClosureTyId::new(k - 1))],
        });
    }
    module
}

/// The chains' roots, and what (handle, closure, bool lane) answer at the
/// top of a seeded chain and of an unseeded one.
fn chain_roots(top: u32) -> [(Ty, [bool; 3], [bool; 3]); 6] {
    [
        (s(top), [true; 3], [false; 3]),
        (Ty::Enum(EnumId::new(top)), [true; 3], [false; 3]),
        // The bool walk never enters a record.
        (
            Ty::Record(RecordId::new(top)),
            [true, true, false],
            [false; 3],
        ),
        (Ty::Array(TyId::new(top), 1), [true; 3], [false; 3]),
        // A signature holds nothing by value.
        (
            Ty::Func(FuncTyId::new(top)),
            [true, false, false],
            [false; 3],
        ),
        // A closure is itself the closure seed, and the by-value walks stop
        // there.
        (
            Ty::Closure(ClosureTyId::new(top)),
            [true, true, false],
            [false, true, false],
        ),
    ]
}

fn reach_answers(table: &LayoutTable<'_>, ty: &Ty) -> [bool; 3] {
    [
        table.type_reaches_handle(ty),
        table.type_holds_closure_by_value(ty),
        table.type_stores_bool_lane(ty),
    ]
}

#[test]
fn deep_chains_are_decided_in_linear_work_on_a_small_stack() {
    // Against the oracle while it is still cheap.
    for seeded in [false, true] {
        let small = chains(40, seeded);
        let mut queries = Vec::new();
        for (ty, _, _) in chain_roots(39) {
            ask_all(&mut queries, ty.clone());
            queries.push(Query::Cast(CastOp::Transmute, ty.clone(), Ty::U64));
            queries.push(Query::Cast(CastOp::Bitcast, ty, Ty::U8));
        }
        let mut rng = Rng(0xdee9);
        let orders = orders(&mut rng, queries.len(), 3);
        compare("chains", &small, &queries, &orders, &mut Census::default());
    }

    // The work bound FIRST, at a depth where a quadratic memo still
    // finishes, so a regression fails here instead of in the deep run below.
    let check = |depth: u32, seeded: bool| {
        let module = chains(depth, seeded);
        let table = module.layout_table();
        for (ty, when_seeded, unseeded) in chain_roots(depth - 1) {
            let want = if seeded { when_seeded } else { unseeded };
            assert_eq!(reach_answers(&table, &ty), want, "{ty:?} seeded={seeded}");
        }
        let stats = table.stats();
        let nodes = 6 * depth as usize;
        // Each node is decided at most once per predicate.
        assert!(stats.reach_nodes <= 3 * nodes, "{stats:?}");
        // A bounded number of steps per node, member and propagation.
        assert!(stats.reach_steps <= 3 * 8 * nodes as u64, "{stats:?}");
        assert!(
            stats.reach_rows_indexed
                <= module.structs.len() + module.enums.len() + module.records.len(),
            "{stats:?}"
        );
        // Every other root costs O(1): a lookup, or (a seeded closure chain,
        // whose top was decided through its signature without deciding the
        // closure it captures) one node whose members are decided.
        let roots = 6 * u64::from(depth.div_ceil(997));
        for k in (0..depth).step_by(997) {
            for (ty, _, _) in chain_roots(k) {
                reach_answers(&table, &ty);
            }
        }
        let after = table.stats();
        assert!(
            after.reach_steps - stats.reach_steps <= 3 * 16 * roots,
            "{after:?}"
        );
        assert!(
            after.reach_nodes - stats.reach_nodes <= 3 * roots as usize,
            "{after:?}"
        );
    };
    check(2000, true);
    check(2000, false);

    // The old walks recursed (overflowing 8 MiB at 10^5) and rescanned the
    // definition lists per level; the memo walks on the heap.
    let worker = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(move || {
            check(100_000, true);
            check(100_000, false);
            // The one-shot `Module` calls are heap walks too.
            let module = chains(100_000, true);
            assert!(module.type_reaches_handle(&s(99_999)));
            assert!(module.type_holds_closure_by_value(&s(99_999)));
            assert!(module.type_stores_bool_lane(&s(99_999)));
            assert!(
                module
                    .callable_carriers(&Ty::Closure(ClosureTyId::new(99_999)))
                    .carries_typed_callable()
            );
        })
        .expect("spawn");
    worker.join().expect("no stack overflow");
}

/// `P{k+1} = {Pk, Pk}`, `Pk` zero-sized; `P0` holds the seeds when `seeded`.
fn doubling(depth: u32, seeded: bool) -> Module {
    let mut module = Module::new("doubling");
    let seeds = if seeded {
        vec![handle(), Ty::Closure(ClosureTyId::new(0)), Ty::Bool]
    } else {
        Vec::new()
    };
    module.structs.push(strukt(0, seeds));
    for k in 1..=depth {
        module.structs.push(strukt(k, vec![s(k - 1), s(k - 1)]));
    }
    module
}

#[test]
fn shared_sub_types_are_decided_once() {
    for seeded in [false, true] {
        let small = doubling(12, seeded);
        let mut queries = Vec::new();
        for k in 0..=12 {
            ask_all(&mut queries, s(k));
        }
        let mut rng = Rng(0xd0b1e);
        let orders = orders(&mut rng, queries.len(), 2);
        compare(
            "doubling",
            &small,
            &queries,
            &orders,
            &mut Census::default(),
        );
    }
    let check = |depth: u32, seeded: bool| {
        let module = doubling(depth, seeded);
        let table = module.layout_table();
        assert_eq!(reach_answers(&table, &s(depth)), [seeded; 3]);
        let stats = table.stats();
        let fields = 2 * u64::from(depth) + 3;
        assert_eq!(stats.reach_nodes, 3 * (depth as usize + 1), "{stats:?}");
        assert!(stats.reach_steps <= 3 * 4 * fields + 32, "{stats:?}");
        assert!(
            stats.reach_rows_indexed <= module.structs.len(),
            "{stats:?}"
        );
    };
    check(20, true);
    check(20, false);
    check(100_000, true);
    check(100_000, false);
}

#[test]
fn a_pass_judging_every_cast_of_a_deep_chain_is_linear() {
    // The validator's cast pass and a bundle's cast facts ask one table per
    // module: one cast per level of a chain used to re-walk the chain below
    // it three times (4000 levels: 77 s); now each node is decided once.
    let check = |depth: u32| {
        let module = chains(depth, true);
        let table = module.layout_table();
        for k in 0..depth {
            let evidence = table.layout_sensitive_cast_evidence(CastOp::Bitcast, &s(k), &Ty::U64);
            assert!(
                matches!(evidence, Err(LayoutError::OpaqueHandleCast { .. })),
                "{k}: {evidence:?}"
            );
            let evidence = table.layout_sensitive_cast_evidence(
                CastOp::Transmute,
                &Ty::Record(RecordId::new(k)),
                &Ty::Record(RecordId::new(k)),
            );
            assert!(
                matches!(evidence, Err(LayoutError::OpaqueHandleCast { .. })),
                "{k}: {evidence:?}"
            );
        }
        let stats = table.stats();
        assert!(stats.reach_nodes <= 2 * depth as usize, "{stats:?}");
        assert!(stats.reach_steps <= 32 * u64::from(depth), "{stats:?}");
        assert!(
            stats.reach_rows_indexed <= module.structs.len() + module.records.len(),
            "{stats:?}"
        );
    };
    check(2000);
    check(100_000);

    // Unseeded, the casts reach the layouts: same-size between the chain's
    // structs (each one word), refused against a byte.
    let module = chains(1000, false);
    let table = module.layout_table();
    for k in 0..1000 {
        assert!(matches!(
            table.layout_sensitive_cast_evidence(CastOp::Bitcast, &s(k), &Ty::U64),
            Ok(CastLayoutEvidence::SameSize { size_bits: 64, .. })
        ));
        assert!(matches!(
            table.layout_sensitive_cast_evidence(CastOp::Transmute, &s(k), &Ty::U8),
            Err(LayoutError::CastSizeMismatch { .. })
        ));
    }
    let stats = table.stats();
    assert!(stats.reach_steps <= 32 * 1000, "{stats:?}");
}

#[test]
fn a_lent_memo_keeps_its_verdicts_until_the_signature_table_moves() {
    let mut module = chains(50, false);
    let table = module.layout_table();
    assert!(!table.type_reaches_handle(&Ty::Func(FuncTyId::new(49))));
    assert!(!table.type_holds_closure_by_value(&s(49)));
    // A signature the module does not have yet: no members, so "no".
    assert!(!table.type_reaches_handle(&Ty::Func(FuncTyId::new(50))));
    assert!(table.ty_layout(&s(49)).is_ok());
    let laid = table.stats().nodes;
    let decided = table.stats().reach_nodes;
    assert!(laid > 0 && decided > 0);
    let memo = table.into_memo();

    // Same tables: the verdicts are kept (a repeat question is a lookup).
    let table = LayoutTable::with_memo(&module, memo);
    assert_eq!(table.stats().reach_nodes, decided);
    assert!(!table.type_reaches_handle(&Ty::Func(FuncTyId::new(49))));
    assert_eq!(table.stats().reach_nodes, decided);
    let memo = table.into_memo();

    // A signature appended: a question that had met a missing signature
    // could now reach a handle, so the reachability verdicts are dropped
    // (and the layouts kept).
    module.func_types.push(FuncTy {
        params: vec![handle()],
        returns: Vec::new(),
        abi: None,
        is_vararg: false,
    });
    let table = LayoutTable::with_memo(&module, memo);
    assert_eq!(table.stats().reach_nodes, 0);
    assert_eq!(table.stats().nodes, laid);
    assert!(table.type_reaches_handle(&Ty::Func(FuncTyId::new(50))));
    assert!(!table.type_reaches_handle(&Ty::Func(FuncTyId::new(49))));

    // A struct appended: every verdict and layout is dropped.
    let memo = table.into_memo();
    module.structs.push(strukt(50, vec![handle()]));
    let table = LayoutTable::with_memo(&module, memo);
    assert_eq!(table.stats().reach_nodes, 0);
    assert_eq!(table.stats().nodes, 0);
}

// Storage policy is a distinct epoch; preserve every original seeded query.
#[path = "by_value_reach_differential/storage_epoch.rs"]
mod storage_epoch;
