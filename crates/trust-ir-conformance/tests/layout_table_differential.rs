// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The module layout table (`trust_ir::LayoutTable`, behind
//! `Module::ty_layout_shape` / `enum_layout_shape` /
//! `struct_field_offset_bits`) against the recursion it replaced, kept
//! verbatim as the oracle in `layout_table_oracle/`.
//!
//! The table memoizes a walk whose cycle refusals depend on where the walk
//! entered, so "identical" is checked from every entry point and in many
//! query orders: each query is answered by the oracle, by the `Module`
//! method (a fresh table per call), and by tables SHARED across all of a
//! module's queries — one per query order, each asked every query twice (the
//! second pass reads the memo).
//!
//! * the fixture corpus (every JSON and text module under `tests/fixtures`);
//! * random type graphs: structs, enums, records, type-table entries and
//!   declared tuple layouts referencing each other by id (missing ids,
//!   duplicate ids, duplicate tuple types, inline copies of declared tuples,
//!   by-value cycles through all four kinds and through records, declared
//!   layouts mostly coherent by construction and then perturbed, niche and
//!   untagged descriptors over `!` fields), and closure types with declared
//!   closure layouts (wire v58: coherent by construction, perturbed, stray,
//!   duplicated, self-capturing), on four targets, in nine query orders each;
//! * every query order of hand-built cycles (rings, figure eights, tails,
//!   a field failing before the cycle edge, a cycle through all four kinds);
//! * the shapes the recursion could not take: `P{k+1} = {Pk, Pk}` (2^k
//!   paths), chains 100 000 deep on a 256 KiB stack, and a niche enum over
//!   a wide (2^16 fields) or deep (10^5 levels) uninhabited payload, with the
//!   table's work counters held to a linear bound.
//!
//! Inhabitedness (the niche rule's question, and the table's own
//! `ty_is_uninhabited` / `variant_is_uninhabited`) is checked against the
//! oracle's naive least fixpoint, and the recursion it replaced against both:
//! equal wherever the question's reach is acyclic, never above the least
//! fixpoint, and below it only on a cyclic reach.

mod layout_table_oracle;

use layout_table_oracle as oracle;
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use trust_ir::ty::{
    ClosureTy, EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant,
    FatPtrKind, FieldDef, RecordDef, SetRepr, StructDef, StructRepr, Ty,
};
use trust_ir::value::{ClosureTyId, EnumId, FuncTyId, PredId, RecordId, StructId, TyId};
use trust_ir::{
    ClosureLayoutDescriptor, Endianness, EnumLayoutShape, LayoutError, LayoutTable, Module,
    TargetInfo, TupleLayoutDescriptor, TyLayoutShape,
};

// ---------------------------------------------------------------------------
// Queries and the comparison
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
enum Query {
    Ty(Ty),
    Enum(EnumId),
    FieldOffset(StructId, u32),
    TupleLayouts,
    ClosureLayouts,
    /// Is this type uninhabited?
    Uninhabited(Ty),
    /// Is variant `.1` of the enum DEFINITION at index `.0` uninhabited?
    Variant(usize, usize),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Answer {
    Ty(Result<TyLayoutShape, LayoutError>),
    Enum(Result<EnumLayoutShape, LayoutError>),
    FieldOffset(Result<u64, LayoutError>),
    TupleLayouts(Result<(), LayoutError>),
    ClosureLayouts(Result<(), LayoutError>),
    Uninhabited(bool),
}

impl Answer {
    fn error(&self) -> Option<&LayoutError> {
        match self {
            Answer::Ty(Err(error))
            | Answer::Enum(Err(error))
            | Answer::FieldOffset(Err(error))
            | Answer::TupleLayouts(Err(error))
            | Answer::ClosureLayouts(Err(error)) => Some(error),
            _ => None,
        }
    }
}

fn ask_oracle(module: &Module, fixpoint: &oracle::LeastFixpoint<'_>, query: &Query) -> Answer {
    match query {
        Query::Ty(ty) => Answer::Ty(oracle::ty_layout_shape(module, ty)),
        Query::Enum(id) => Answer::Enum(oracle::enum_layout_shape(module, *id)),
        Query::FieldOffset(id, field) => {
            Answer::FieldOffset(oracle::struct_field_offset_bits(module, *id, *field))
        }
        Query::TupleLayouts => Answer::TupleLayouts(oracle_validate_tuple_layouts(module)),
        Query::ClosureLayouts => Answer::ClosureLayouts(oracle_validate_closure_layouts(module)),
        Query::Uninhabited(ty) => Answer::Uninhabited(fixpoint.ty_is_uninhabited(ty)),
        Query::Variant(def, variant) => Answer::Uninhabited(
            fixpoint.variant_is_uninhabited(&module.enums[*def].variants[*variant]),
        ),
    }
}

/// `Module::validate_tuple_layouts` before the table: one recursion per row.
fn oracle_validate_tuple_layouts(module: &Module) -> Result<(), LayoutError> {
    for desc in &module.tuple_layouts {
        let ty = module
            .types
            .get(desc.tuple_type.as_usize())
            .ok_or(LayoutError::MissingType(desc.tuple_type))?;
        if !matches!(ty, Ty::Tuple(_)) {
            return Err(LayoutError::TupleLayoutIncoherent(desc.tuple_type));
        }
        oracle::ty_layout_shape(module, ty)?;
    }
    Ok(())
}

/// `Module::validate_closure_layouts` as the recursion states it: one walk
/// per row.
fn oracle_validate_closure_layouts(module: &Module) -> Result<(), LayoutError> {
    for desc in &module.closure_layouts {
        if module.closure_type(desc.closure).is_none() {
            return Err(LayoutError::ClosureLayoutIncoherent(desc.closure));
        }
        oracle::ty_layout_shape(module, &Ty::Closure(desc.closure))?;
    }
    Ok(())
}

fn ask_module(module: &Module, query: &Query) -> Answer {
    match query {
        Query::Ty(ty) => Answer::Ty(module.ty_layout_shape(ty)),
        Query::Enum(id) => Answer::Enum(module.enum_layout_shape(*id)),
        Query::FieldOffset(id, field) => {
            Answer::FieldOffset(module.struct_field_offset_bits(*id, *field))
        }
        Query::TupleLayouts => Answer::TupleLayouts(module.validate_tuple_layouts()),
        Query::ClosureLayouts => Answer::ClosureLayouts(module.validate_closure_layouts()),
        Query::Uninhabited(ty) => Answer::Uninhabited(module.ty_is_uninhabited(ty)),
        Query::Variant(def, variant) => Answer::Uninhabited(
            module.variant_is_uninhabited(&module.enums[*def].variants[*variant]),
        ),
    }
}

fn ask_table(table: &LayoutTable<'_>, query: &Query) -> Answer {
    match query {
        Query::Ty(ty) => Answer::Ty(table.ty_layout_shape(ty)),
        Query::Enum(id) => Answer::Enum(table.enum_layout_shape(*id)),
        Query::FieldOffset(id, field) => {
            Answer::FieldOffset(table.struct_field_offset_bits(*id, *field))
        }
        Query::TupleLayouts => Answer::TupleLayouts(table.validate_tuple_layouts()),
        Query::ClosureLayouts => Answer::ClosureLayouts(table.validate_closure_layouts()),
        Query::Uninhabited(ty) => Answer::Uninhabited(table.ty_is_uninhabited(ty)),
        Query::Variant(def, variant) => Answer::Uninhabited(
            table.variant_is_uninhabited(&table.module().enums[*def].variants[*variant]),
        ),
    }
}

/// What a comparison run saw, so a vacuous corpus fails.
#[derive(Default, Debug)]
struct Census {
    modules: usize,
    queries: usize,
    laid_out: usize,
    errors: BTreeMap<&'static str, usize>,
    uninhabited: usize,
    inhabited: usize,
}

fn error_name(error: &LayoutError) -> &'static str {
    match error {
        LayoutError::MissingType(_) => "MissingType",
        LayoutError::MissingStruct(_) => "MissingStruct",
        LayoutError::MissingStructSize(_) => "MissingStructSize",
        LayoutError::MissingStructAlign(_) => "MissingStructAlign",
        LayoutError::StructLayoutIncoherent(_) => "StructLayoutIncoherent",
        LayoutError::TupleLayoutIncoherent(_) => "TupleLayoutIncoherent",
        LayoutError::TupleLayoutTargetMissing => "TupleLayoutTargetMissing",
        LayoutError::ClosureLayoutIncoherent(_) => "ClosureLayoutIncoherent",
        LayoutError::ClosureLayoutTargetMissing => "ClosureLayoutTargetMissing",
        LayoutError::TargetScalarLayoutUnavailable { .. } => "TargetScalarLayoutUnavailable",
        LayoutError::MissingFieldOffset { .. } => "MissingFieldOffset",
        LayoutError::EnumLayoutUnavailable(_) => "EnumLayoutUnavailable",
        LayoutError::TyLayoutCycle(_) => "TyLayoutCycle",
        LayoutError::UnsupportedTyShape(_) => "UnsupportedTyShape",
        LayoutError::SizeOverflow => "SizeOverflow",
        _ => "other",
    }
}

/// Every query, answered by the oracle, by the `Module` methods, and by one
/// table per order in `orders`, shared across the module's queries and asked
/// every query twice in that order (the second pass reads the memo), must
/// agree.
fn compare(
    label: &str,
    module: &Module,
    queries: &[Query],
    orders: &[Vec<usize>],
    census: &mut Census,
) {
    let fixpoint = oracle::least_fixpoint(module);
    let want: Vec<Answer> = queries
        .iter()
        .map(|q| ask_oracle(module, &fixpoint, q))
        .collect();
    for (query, want) in queries.iter().zip(&want) {
        let got = ask_module(module, query);
        assert_eq!(&got, want, "{label}: Module answer for {query:?}");
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
    for answer in &want {
        match answer {
            Answer::Uninhabited(true) => census.uninhabited += 1,
            Answer::Uninhabited(false) => census.inhabited += 1,
            _ => match answer.error() {
                Some(error) => *census.errors.entry(error_name(error)).or_default() += 1,
                None => census.laid_out += 1,
            },
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

/// The queries a module invites: every nominal id it defines and one it does
/// not (the ids PRESENT, so a sparse id costs one query, never the id range),
/// every type-table entry inline and through `Array` / `Refine`, every field
/// offset and every struct, enum and record field type, the declared tuple
/// rows, every closure type (and one absent) and the declared closure rows,
/// a few inline wrappers, and the inhabitedness of every id, entry,
/// field type and variant.
fn module_queries(module: &Module) -> Vec<Query> {
    let mut queries = Vec::new();
    let mut struct_ids: Vec<u32> = module.structs.iter().map(|def| def.id.index()).collect();
    struct_ids.sort_unstable();
    struct_ids.dedup();
    let absent_struct = struct_ids.last().map_or(Some(0), |id| id.checked_add(1));
    for id in struct_ids.iter().copied().chain(absent_struct) {
        let id = StructId::new(id);
        queries.push(Query::Ty(Ty::Struct(id)));
        queries.push(Query::Ty(Ty::Vector(Box::new(Ty::Struct(id)), 2)));
        queries.push(Query::Uninhabited(Ty::Struct(id)));
        let fields = module
            .structs
            .iter()
            .find(|def| def.id == id)
            .map_or(0, |def| def.fields.len() as u32);
        for field in 0..=fields {
            queries.push(Query::FieldOffset(id, field));
        }
    }
    let mut enum_ids: Vec<u32> = module.enums.iter().map(|def| def.id.index()).collect();
    enum_ids.sort_unstable();
    enum_ids.dedup();
    let absent_enum = enum_ids.last().map_or(Some(0), |id| id.checked_add(1));
    for id in enum_ids.iter().copied().chain(absent_enum) {
        queries.push(Query::Ty(Ty::Enum(EnumId::new(id))));
        queries.push(Query::Enum(EnumId::new(id)));
        queries.push(Query::Uninhabited(Ty::Enum(EnumId::new(id))));
    }
    let mut record_ids: Vec<u32> = module.records.iter().map(|def| def.id.index()).collect();
    record_ids.sort_unstable();
    record_ids.dedup();
    let absent_record = record_ids.last().map_or(Some(0), |id| id.checked_add(1));
    for id in record_ids.iter().copied().chain(absent_record) {
        queries.push(Query::Uninhabited(Ty::Record(RecordId::new(id))));
    }
    for index in 0..=module.types.len() {
        let id = TyId::new(index as u32);
        if let Some(ty) = module.types.get(index) {
            queries.push(Query::Ty(ty.clone()));
            queries.push(Query::Uninhabited(ty.clone()));
        }
        queries.push(Query::Ty(Ty::Array(id, 2)));
        queries.push(Query::Ty(Ty::Refine(id, PredId::new(0))));
        queries.push(Query::Uninhabited(Ty::Array(id, 2)));
        queries.push(Query::Uninhabited(Ty::Array(id, 0)));
        queries.push(Query::Uninhabited(Ty::Refine(id, PredId::new(0))));
    }
    // What the validator asks: every field type, as written.
    let mut field_types: BTreeSet<String> = BTreeSet::new();
    let mut field_type = |queries: &mut Vec<Query>, ty: &Ty| {
        if field_types.insert(format!("{ty:?}")) {
            queries.push(Query::Ty(ty.clone()));
            queries.push(Query::Uninhabited(ty.clone()));
        }
    };
    for def in &module.structs {
        for field in &def.fields {
            field_type(&mut queries, &field.ty);
        }
    }
    for def in &module.records {
        for field in &def.fields {
            field_type(&mut queries, &field.ty);
        }
    }
    for (index, def) in module.enums.iter().enumerate() {
        for (variant_index, variant) in def.variants.iter().enumerate() {
            queries.push(Query::Variant(index, variant_index));
            for ty in &variant.fields {
                field_type(&mut queries, ty);
            }
        }
    }
    for def in &module.closure_types {
        for capture in &def.captures {
            field_type(&mut queries, capture);
        }
    }
    for index in 0..=module.closure_types.len() {
        let closure = Ty::Closure(ClosureTyId::new(index as u32));
        queries.push(Query::Ty(Ty::Vector(Box::new(closure.clone()), 2)));
        queries.push(Query::Ty(closure));
    }
    queries.push(Query::TupleLayouts);
    queries.push(Query::ClosureLayouts);
    queries.push(Query::Ty(Ty::Tuple(Vec::new())));
    queries.push(Query::Uninhabited(Ty::Never));
    queries.push(Query::Uninhabited(Ty::Tuple(vec![Ty::U8, Ty::Never])));
    // The tensor region (PKG-U13a): a tensor has no layout, and is inhabited
    // whatever its element (an extent may be 0).
    queries.push(Query::Ty(Ty::Tensor(Box::new(Ty::I32), 2)));
    queries.push(Query::Uninhabited(Ty::Tensor(Box::new(Ty::Never), 1)));
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
fn the_fixture_corpus_lays_out_exactly_as_the_recursion_did() {
    let mut census = Census::default();
    let mut rng = Rng(0x1a70_7ab1e);
    for (name, module) in corpus_modules() {
        let queries = module_queries(&module);
        let orders = orders(&mut rng, queries.len(), 1);
        compare(&name, &module, &queries, &orders, &mut census);
    }
    eprintln!("fixture corpus: {census:?}");
    // Not vacuous: the corpus decodes, and it holds layouts and refusals.
    assert!(census.modules >= 100, "{census:?}");
    assert!(census.laid_out >= 100, "{census:?}");
    assert!(census.errors.len() >= 4, "{census:?}");
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

struct Gen {
    rng: Rng,
    types: u32,
    structs: u32,
    enums: u32,
    records: u32,
    /// Percent of generated types that are `!` (beyond the leaf's share), so
    /// some modules are dense in uninhabited fields.
    never: u64,
}

impl Gen {
    fn leaf(&mut self) -> Ty {
        match self.rng.below(30) {
            0 => Ty::Bool,
            1 => Ty::I8,
            2 => Ty::I16,
            3 => Ty::I32,
            4 => Ty::I64,
            5 => Ty::I128,
            6 => Ty::U8,
            7 => Ty::U32,
            8 => Ty::U64,
            9 => Ty::U128,
            10 => Ty::Isize,
            11 => Ty::Usize,
            12 => Ty::Char,
            13 => Ty::F16,
            14 => Ty::F32,
            15 => Ty::F64,
            16 => Ty::Ptr,
            17 => Ty::Unit,
            18 => Ty::Never,
            19 => Ty::FatPtr(FatPtrKind::Str),
            20 => Ty::FatPtr(FatPtrKind::Slice(TyId::new(0))),
            21 => Ty::Ref(Box::new(Ty::U8)),
            22 => Ty::Func(FuncTyId::new(0)),
            23 => Ty::Error,
            24 => Ty::Closure(ClosureTyId::new(0)),
            25 => Ty::Record(RecordId::new(
                self.rng.below(u64::from(self.records) + 1) as u32
            )),
            26 => Ty::Sequence(TyId::new(0)),
            27 => Ty::Set(TyId::new(0), SetRepr::Bitset),
            28 => Ty::PtrMut(Box::new(Ty::Struct(StructId::new(0)))),
            _ => Ty::U16,
        }
    }

    fn len(&mut self) -> u64 {
        match self.rng.below(20) {
            0 => u64::MAX / 3,
            1 => 1 << 40,
            n => n % 4,
        }
    }

    fn ty(&mut self, depth: u32) -> Ty {
        let types = u64::from(self.types) + 1;
        if self.rng.chance(self.never) {
            return Ty::Never;
        }
        match self.rng.below(100) {
            0..=29 => self.leaf(),
            30..=45 => Ty::Struct(StructId::new(
                self.rng.below(u64::from(self.structs) + 1) as u32
            )),
            46..=57 => Ty::Enum(EnumId::new(self.rng.below(u64::from(self.enums) + 1) as u32)),
            58..=68 => {
                let len = self.len();
                Ty::Array(TyId::new(self.rng.below(types) as u32), len)
            }
            69..=76 => Ty::Refine(TyId::new(self.rng.below(types) as u32), PredId::new(0)),
            77..=86 if depth > 0 => {
                let lanes = self.rng.below(4) as u32 + u32::from(self.rng.chance(90));
                Ty::Vector(Box::new(self.ty(depth - 1)), lanes)
            }
            87..=99 if depth > 0 => {
                let n = self.rng.below(4);
                Ty::Tuple((0..n).map(|_| self.ty(depth - 1)).collect())
            }
            _ => self.leaf(),
        }
    }

    fn repr(&mut self) -> EnumTagRepr {
        [
            EnumTagRepr::U8,
            EnumTagRepr::U16,
            EnumTagRepr::U32,
            EnumTagRepr::U64,
            EnumTagRepr::I8,
            EnumTagRepr::I16,
            EnumTagRepr::I32,
            EnumTagRepr::I64,
            EnumTagRepr::U128,
            EnumTagRepr::I128,
        ][self.rng.below(10) as usize]
    }
}

fn target(rng: &mut Rng) -> Option<TargetInfo> {
    let (triple, pointer_size) = match rng.below(10) {
        0..=2 => return None,
        3..=6 => ("x86_64-unknown-linux-gnu", 8),
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

/// A field's byte size and alignment by the oracle, if it has a usable one.
fn field_bytes(module: &Module, ty: &Ty) -> Option<(u64, u64)> {
    let layout = oracle::ty_layout_shape(module, ty).ok()?;
    let size = layout.size_bytes()?;
    let align = layout
        .align_bits
        .filter(|bits| *bits != 0 && bits.is_multiple_of(8))?
        / 8;
    Some((size, align))
}

/// [`field_bytes`] for an enum descriptor's payload, where a direct `!`
/// field is size 0, align 1 (rustc's `B(!)`).
fn payload_bytes(module: &Module, ty: &Ty) -> Option<(u64, u64)> {
    if matches!(ty, Ty::Never) {
        return Some((0, 1));
    }
    field_bytes(module, ty)
}

fn align_up(offset: u64, align: u64) -> Option<u64> {
    offset.checked_next_multiple_of(align)
}

/// C-style placement of `fields` from `start`: their offsets, the end, and
/// the max alignment — or `None` when a field has no usable layout.
fn c_layout(module: &Module, fields: &[Ty], start: u64) -> Option<(Vec<u64>, u64, u64)> {
    c_layout_with(module, fields, start, field_bytes)
}

fn c_layout_with(
    module: &Module,
    fields: &[Ty],
    start: u64,
    bytes: fn(&Module, &Ty) -> Option<(u64, u64)>,
) -> Option<(Vec<u64>, u64, u64)> {
    let mut offset = start;
    let mut max_align = 1;
    let mut offsets = Vec::with_capacity(fields.len());
    for ty in fields {
        let (size, align) = bytes(module, ty)?;
        offset = align_up(offset, align)?;
        offsets.push(offset);
        offset = offset.checked_add(size)?;
        max_align = max_align.max(align);
    }
    Some((offsets, offset, max_align))
}

fn random_module(seed: u64) -> Module {
    let mut g = Gen {
        rng: Rng(seed),
        types: 0,
        structs: 0,
        enums: 0,
        records: 0,
        never: 0,
    };
    g.types = g.rng.below(7) as u32;
    g.structs = g.rng.below(7) as u32;
    g.enums = g.rng.below(5) as u32;
    g.records = g.rng.below(4) as u32;
    if g.rng.chance(30) {
        g.never = g.rng.below(25);
    }
    let mut module = Module::new(format!("random-{seed}"));
    module.target_info = target(&mut g.rng);
    for _ in 0..g.types {
        let ty = g.ty(2);
        module.types.push(ty);
    }
    // A second entry spelling a tuple the table already holds: two rows can
    // then declare one tuple through different ids.
    if g.rng.chance(15)
        && let Some(tuple) = module
            .types
            .iter()
            .find(|ty| matches!(ty, Ty::Tuple(_)))
            .cloned()
    {
        module.types.push(tuple);
        g.types += 1;
    }
    let tuples: Vec<Ty> = module
        .types
        .iter()
        .filter(|ty| matches!(ty, Ty::Tuple(_)))
        .cloned()
        .collect();
    for index in 0..g.structs {
        let id = if index > 0 && g.rng.chance(10) {
            module.structs[g.rng.below(u64::from(index)) as usize].id
        } else {
            StructId::new(index)
        };
        let fields = (0..g.rng.below(4))
            .map(|field| FieldDef {
                name: format!("f{field}"),
                // An inline copy of a declared tuple resolves to its row.
                ty: if !tuples.is_empty() && g.rng.chance(10) {
                    tuples[g.rng.below(tuples.len() as u64) as usize].clone()
                } else {
                    g.ty(1)
                },
                offset: None,
            })
            .collect();
        let repr = match g.rng.below(20) {
            0 => StructRepr::Transparent,
            1 => StructRepr::Packed(1),
            2 => StructRepr::Packed(3),
            3 => StructRepr::C,
            _ => StructRepr::Rust,
        };
        module.structs.push(StructDef {
            id,
            name: format!("S{index}"),
            fields,
            size: None,
            align: None,
            repr,
            origin: None,
        });
    }
    for index in 0..g.enums {
        let id = if index > 0 && g.rng.chance(10) {
            module.enums[g.rng.below(u64::from(index)) as usize].id
        } else {
            EnumId::new(index)
        };
        let variants: Vec<EnumVariant> = (0..g.rng.below(4) + u64::from(g.rng.chance(90)))
            .map(|variant| EnumVariant {
                name: format!("V{variant}"),
                fields: (0..g.rng.below(3)).map(|_| g.ty(1)).collect(),
                field_names: Vec::new(),
            })
            .collect();
        let mut def = EnumDef::new(id, format!("E{index}"), variants);
        if g.rng.chance(15) {
            def.discriminants = (0..def.variants.len())
                .map(|_| g.rng.chance(60).then(|| g.rng.below(300) as i128 - 3))
                .collect();
        }
        if g.rng.chance(15) {
            def.repr = Some(g.repr());
        }
        module.enums.push(def);
    }
    // Often a void enum `{ V(!) }`, declared untagged and zero-sized, at the
    // one id `ty` names past the generated enums: it lays out and is
    // uninhabited, so a struct or variant holding it is too.
    let void = g.rng.chance(40).then(|| EnumId::new(g.enums));
    if let Some(id) = void {
        let mut def = EnumDef::new(
            id,
            "Void",
            vec![EnumVariant {
                name: "V".into(),
                fields: vec![Ty::Never],
                field_names: Vec::new(),
            }],
        );
        def.layout = Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Untagged,
            size: 0,
            align: 1,
            variant_field_offsets: vec![vec![0]],
        });
        module.enums.push(def);
    }
    for index in 0..g.records {
        let id = if index > 0 && g.rng.chance(15) {
            module.records[g.rng.below(u64::from(index)) as usize].id
        } else {
            RecordId::new(index)
        };
        let fields = (0..g.rng.below(4))
            .map(|field| FieldDef {
                name: format!("r{field}"),
                ty: g.ty(1),
                offset: None,
            })
            .collect();
        module.records.push(RecordDef {
            id,
            name: format!("R{index}"),
            fields,
        });
    }

    // Declared struct layouts: lay out, bottom-up by fixpoint, every struct
    // whose fields the oracle can lay out, C-style; most stay coherent.
    let mut changed = true;
    while changed {
        changed = false;
        for index in g.rng.permutation(module.structs.len()) {
            if module.structs[index].size.is_some() {
                continue;
            }
            let tys: Vec<Ty> = module.structs[index]
                .fields
                .iter()
                .map(|field| field.ty.clone())
                .collect();
            let Some((offsets, end, align)) = c_layout(&module, &tys, 0) else {
                continue;
            };
            let align = match module.structs[index].repr {
                StructRepr::Packed(_) => 1,
                _ => align,
            };
            let Some(size) = align_up(end, align) else {
                continue;
            };
            let def = &mut module.structs[index];
            for (field, offset) in def.fields.iter_mut().zip(offsets) {
                field.offset = Some(offset);
            }
            def.size = Some(size);
            def.align = Some(align);
            changed = true;
        }
    }
    for def in &mut module.structs {
        // Most size-less structs (those on a cycle, or over a field with no
        // layout) get a plausible declaration, so walks reach the cycle edge.
        if def.size.is_none() && g.rng.chance(85) {
            def.size = Some(g.rng.below(17));
            def.align = Some(1 << g.rng.below(4));
            for field in &mut def.fields {
                field.offset = g.rng.chance(80).then(|| g.rng.below(9));
            }
        }
        if def.size.is_some() && g.rng.chance(15) {
            match g.rng.below(7) {
                0 => def.size = def.size.map(|size| size + 1),
                1 => def.align = def.align.map(|align| align * 2),
                2 => def.size = def.size.and_then(|size| size.checked_sub(1)),
                3 => def.align = None,
                _ => {
                    if let Some(field) = def.fields.first_mut() {
                        field.offset = match g.rng.below(3) {
                            0 => None,
                            1 => field.offset.map(|offset| offset + 1),
                            _ => Some(u64::MAX - 1),
                        };
                    }
                }
            }
        }
    }

    // Declared enum layouts: the canonical image restated as a `Direct`
    // descriptor, a single variant as `Untagged`, or a random `Niche` — also
    // for an enum with no canonical layout (a direct `!` field is size 0,
    // align 1 under a descriptor), so the niche rule meets uninhabited
    // variants.
    for index in 0..module.enums.len() {
        if module.enums[index].layout.is_some() || !g.rng.chance(50) {
            continue;
        }
        let id = module.enums[index].id;
        let canonical = oracle::enum_layout_shape(&module, id).ok();
        let variants = module.enums[index].variants.clone();
        let encoding = match (g.rng.below(10), &canonical) {
            (0..=5, Some(_)) => EnumTagEncoding::Direct { tag_offset: 0 },
            (0..=1, None) | (6, _) => EnumTagEncoding::Untagged,
            _ => EnumTagEncoding::Niche {
                untagged_variant: g.rng.below(3) as u32,
                niche_variants_start: g.rng.below(2) as u32,
                niche_variants_end: g.rng.below(3) as u32,
                niche_start: u128::from(g.rng.below(4)),
                niche_offset: g.rng.below(4),
                niche_ty: g.repr(),
            },
        };
        let start = match (&encoding, &canonical) {
            (EnumTagEncoding::Direct { .. }, Some(canonical)) => canonical.payload_offset_bits / 8,
            _ => 0,
        };
        let mut offsets = Vec::with_capacity(variants.len());
        let (mut size, mut align) = canonical.as_ref().map_or((0, 1), |canonical| {
            (canonical.size_bits / 8, canonical.align_bits / 8)
        });
        let mut ok = true;
        for variant in &variants {
            match c_layout_with(&module, &variant.fields, start, payload_bytes) {
                Some((placed, end, variant_align)) => {
                    offsets.push(placed);
                    if !matches!(encoding, EnumTagEncoding::Direct { .. }) {
                        align = align.max(variant_align);
                        size = size.max(align_up(end, variant_align).unwrap_or(end));
                    }
                }
                None => ok = false,
            }
        }
        if !ok {
            continue;
        }
        // Most niches are made placeable: a one-byte lane over the first
        // non-empty field of an untagged variant that alone is encoded, so
        // the enum lays out exactly when every other variant is uninhabited.
        let mut encoding = encoding;
        if matches!(encoding, EnumTagEncoding::Niche { .. }) && g.rng.chance(70) {
            let carrier = variants.iter().enumerate().find_map(|(index, variant)| {
                variant.fields.iter().enumerate().find_map(|(field, ty)| {
                    payload_bytes(&module, ty)
                        .filter(|(size, _)| *size > 0)
                        .map(|_| (index, offsets[index][field]))
                })
            });
            if let Some((untagged, niche_offset)) = carrier {
                // Often make the other variants uninhabited, through a `!`
                // or the void enum, so the niche rule must exempt them.
                for (other, offsets) in offsets.iter_mut().enumerate() {
                    if other != untagged && g.rng.chance(60) {
                        let uninhabited = match void {
                            Some(id) if g.rng.chance(70) => Ty::Enum(id),
                            _ => Ty::Never,
                        };
                        module.enums[index].variants[other].fields.push(uninhabited);
                        offsets.push(0);
                    }
                }
                encoding = EnumTagEncoding::Niche {
                    untagged_variant: untagged as u32,
                    niche_variants_start: untagged as u32,
                    niche_variants_end: untagged as u32,
                    niche_start: 0,
                    niche_offset,
                    niche_ty: EnumTagRepr::U8,
                };
            }
        }
        if !matches!(encoding, EnumTagEncoding::Direct { .. }) {
            size = align_up(size, align).unwrap_or(size);
        }
        if g.rng.chance(20) {
            size = size.saturating_sub(1);
        }
        module.enums[index].layout = Some(EnumLayoutDescriptor {
            encoding,
            size,
            align,
            variant_field_offsets: offsets,
        });
    }

    // Declared tuple layouts over the table's tuples, plus stray rows.
    for index in 0..module.types.len() {
        let Ty::Tuple(elems) = module.types[index].clone() else {
            continue;
        };
        if !g.rng.chance(60) {
            continue;
        }
        let (field_offsets, size, align) = match c_layout(&module, &elems, 0) {
            Some((offsets, end, align)) => (offsets, align_up(end, align).unwrap_or(end), align),
            None => (
                elems.iter().map(|_| g.rng.below(8)).collect(),
                g.rng.below(16),
                1 << g.rng.below(3),
            ),
        };
        module.tuple_layouts.push(TupleLayoutDescriptor {
            tuple_type: TyId::new(index as u32),
            size,
            align,
            field_offsets,
        });
    }
    // A stray row (a missing or non-tuple type, or a second row for a tuple)
    // and a duplicate, each anywhere in the list: which one the scan reaches
    // first decides the refusal.
    if g.rng.chance(15) {
        let at = g.rng.below(module.tuple_layouts.len() as u64 + 1) as usize;
        module.tuple_layouts.insert(
            at,
            TupleLayoutDescriptor {
                tuple_type: TyId::new(g.rng.below(u64::from(g.types) + 2) as u32),
                size: 8,
                align: 8,
                field_offsets: vec![0],
            },
        );
    }
    if g.rng.chance(15) && !module.tuple_layouts.is_empty() {
        let row =
            module.tuple_layouts[g.rng.below(module.tuple_layouts.len() as u64) as usize].clone();
        let at = g.rng.below(module.tuple_layouts.len() as u64 + 1) as usize;
        module.tuple_layouts.insert(at, row);
    }

    // Wire v58: closure types and declared closure layouts over them, drawn
    // AFTER everything above so every earlier part of the graph is the one
    // this seed always drew. A capture may name a closure type by value
    // (`Gen::leaf` spells closure 0), so a closure can capture itself.
    for _ in 0..g.rng.below(3) {
        let captures = (0..g.rng.below(4)).map(|_| g.ty(1)).collect();
        module.closure_types.push(ClosureTy {
            func: FuncTyId::new(0),
            captures,
        });
    }
    for index in 0..module.closure_types.len() {
        if !g.rng.chance(70) {
            continue;
        }
        let captures = module.closure_types[index].captures.clone();
        let (capture_offsets, size, align) = match c_layout(&module, &captures, 0) {
            Some((offsets, end, align)) => (offsets, align_up(end, align).unwrap_or(end), align),
            None => (
                captures.iter().map(|_| g.rng.below(8)).collect(),
                g.rng.below(16),
                1 << g.rng.below(3),
            ),
        };
        let mut row = ClosureLayoutDescriptor {
            origin: None,
            closure: ClosureTyId::new(index as u32),
            size,
            align,
            capture_offsets,
        };
        // Perturb a coherent row: a frame one byte short, or two captures
        // swapped (which a reordered `repr(Rust)` frame may legitimately do,
        // and an incoherent one may not).
        if g.rng.chance(20) {
            row.size = row.size.saturating_sub(1);
        }
        if g.rng.chance(20) && row.capture_offsets.len() >= 2 {
            row.capture_offsets.swap(0, 1);
        }
        module.closure_layouts.push(row);
    }
    // A stray row (a closure type the module does not define) and a
    // duplicate, each anywhere in the list.
    if g.rng.chance(15) {
        let at = g.rng.below(module.closure_layouts.len() as u64 + 1) as usize;
        module.closure_layouts.insert(
            at,
            ClosureLayoutDescriptor {
                origin: None,
                closure: ClosureTyId::new(module.closure_types.len() as u32),
                size: 8,
                align: 8,
                capture_offsets: vec![0],
            },
        );
    }
    if g.rng.chance(15) && !module.closure_layouts.is_empty() {
        let row = module.closure_layouts[g.rng.below(module.closure_layouts.len() as u64) as usize]
            .clone();
        let at = g.rng.below(module.closure_layouts.len() as u64 + 1) as usize;
        module.closure_layouts.insert(at, row);
    }
    module
}

/// A niche enum that lays out although a variant lies outside its encoding:
/// the niche rule exempted that variant as uninhabited.
fn niche_exemptions(module: &Module) -> usize {
    module
        .enums
        .iter()
        .filter(|def| {
            let Some(EnumLayoutDescriptor {
                encoding:
                    EnumTagEncoding::Niche {
                        untagged_variant,
                        niche_variants_start,
                        niche_variants_end,
                        ..
                    },
                ..
            }) = &def.layout
            else {
                return false;
            };
            let unencoded = (0..def.variants.len() as u32).any(|index| {
                index != *untagged_variant
                    && !(*niche_variants_start..=*niche_variants_end).contains(&index)
            });
            unencoded && oracle::enum_layout_shape(module, def.id).is_ok()
        })
        .count()
}

#[test]
fn random_type_graphs_lay_out_exactly_as_the_recursion_did() {
    let mut census = Census::default();
    let mut rng = Rng(0x5eed);
    let mut exemptions = 0;
    let mut closure_frames = 0usize;
    for seed in 0..6_000u64 {
        let mut module = random_module(seed);
        exemptions += niche_exemptions(&module);
        closure_frames += module
            .closure_layouts
            .iter()
            .filter(|row| oracle::ty_layout_shape(&module, &Ty::Closure(row.closure)).is_ok())
            .count();
        let mut queries = module_queries(&module);
        let mut generator = Gen {
            rng: Rng(seed ^ 0xabcd),
            types: module.types.len() as u32,
            structs: module.structs.len() as u32,
            enums: module.enums.len() as u32,
            records: module.records.len() as u32,
            never: 5,
        };
        for _ in 0..4 {
            let ty = generator.ty(2);
            queries.push(Query::Uninhabited(ty.clone()));
            queries.push(Query::Ty(ty));
        }
        // Eight shuffled orders and one reversed, each on its own table.
        let orders_here = orders(&mut rng, queries.len(), 8);
        compare(
            &format!("seed {seed}"),
            &module,
            &queries,
            &orders_here,
            &mut census,
        );
        // The same graph again with the target removed or swapped: the
        // scalar refusal and the tuple-target refusal are path-free too.
        module.target_info = target(&mut rng);
        let orders_here = orders(&mut rng, queries.len(), 2);
        compare(
            &format!("seed {seed}, retargeted"),
            &module,
            &queries,
            &orders_here,
            &mut census,
        );
    }
    eprintln!("random graphs: {census:?}");
    // Not vacuous: layouts, and every refusal the walk can produce.
    assert!(census.laid_out * 10 >= census.queries, "{census:?}");
    for name in [
        "MissingType",
        "MissingStruct",
        "MissingStructSize",
        "MissingStructAlign",
        "StructLayoutIncoherent",
        "TupleLayoutIncoherent",
        "TupleLayoutTargetMissing",
        "ClosureLayoutIncoherent",
        "ClosureLayoutTargetMissing",
        "TargetScalarLayoutUnavailable",
        "MissingFieldOffset",
        "EnumLayoutUnavailable",
        "TyLayoutCycle",
        "UnsupportedTyShape",
        "SizeOverflow",
    ] {
        assert!(
            census.errors.get(name).copied().unwrap_or(0) >= 5,
            "{name} never refused: {census:?}"
        );
    }
    // Both inhabitedness verdicts, many times, and the niche rule laying out
    // enums only because a variant outside the encoding is uninhabited.
    assert!(census.uninhabited >= 1_000, "{census:?}");
    assert!(census.inhabited >= 1_000, "{census:?}");
    eprintln!("niche exemptions: {exemptions}");
    assert!(exemptions >= 20, "{exemptions}");
    // Declared closure frames that lay out, not only refusals.
    eprintln!("closure frames laid out: {closure_frames}");
    assert!(closure_frames >= 100, "{closure_frames}");
}

// ---------------------------------------------------------------------------
// Cycles, from every entry point and in every query order
// ---------------------------------------------------------------------------

fn x86_64(name: &str) -> Module {
    let mut module = Module::new(name);
    module.target_info = Some(TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    module
}

fn strukt(id: u32, fields: Vec<Ty>) -> StructDef {
    let size = 8 * fields.len() as u64;
    StructDef {
        id: StructId::new(id),
        name: format!("S{id}"),
        fields: fields
            .into_iter()
            .enumerate()
            .map(|(index, ty)| FieldDef {
                name: format!("f{index}"),
                ty,
                offset: Some(8 * index as u64),
            })
            .collect(),
        size: Some(size),
        align: Some(8),
        repr: StructRepr::C,
        origin: None,
    }
}

fn s(id: u32) -> Ty {
    Ty::Struct(StructId::new(id))
}

/// Every order of `queries` (up to 7! = 5040), each on its own shared table.
fn every_order(label: &str, module: &Module, queries: &[Query]) -> usize {
    let mut census = Census::default();
    let mut order: Vec<usize> = (0..queries.len()).collect();
    let mut count = 0;
    permute(&mut order, 0, &mut |order| {
        compare(label, module, queries, &[order.to_vec()], &mut census);
        count += 1;
    });
    count
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
fn a_cycle_answers_from_every_entry_point_as_the_recursion_did() {
    // A ring A -> B -> C -> A with a laid-out side field before the ring
    // edge, and a tail T -> A: entered at A, B, C or T the recursion names a
    // different re-entered struct, and so must every order of the table.
    let mut ring = x86_64("ring");
    ring.add_struct(strukt(0, vec![Ty::U64, s(1)])); // A: ok field, then B
    ring.add_struct(strukt(1, vec![s(2)])); // B
    ring.add_struct(strukt(2, vec![s(0)])); // C
    ring.add_struct(strukt(3, vec![s(0)])); // T
    ring.add_struct(strukt(4, vec![Ty::U64])); // X: outside
    let queries: Vec<Query> = (0..5).map(|id| Query::Ty(s(id))).collect();
    assert_eq!(every_order("ring", &ring, &queries), 120);

    // A figure eight: A -> B -> A and A -> C -> A, A's B edge first.
    let mut eight = x86_64("figure-eight");
    eight.add_struct(strukt(0, vec![s(1), s(2)]));
    eight.add_struct(strukt(1, vec![s(0)]));
    eight.add_struct(strukt(2, vec![s(0)]));
    let queries: Vec<Query> = (0..3).map(|id| Query::Ty(s(id))).collect();
    every_order("figure-eight", &eight, &queries);

    // A field that fails before the ring edge wins from every entry; one
    // that fails after it never does.
    let mut early = x86_64("early-failure");
    early.add_struct(strukt(0, vec![Ty::Error, s(1)]));
    early.add_struct(strukt(1, vec![s(0)]));
    early.add_struct(strukt(2, vec![s(0), Ty::Error]));
    early.add_struct(strukt(3, vec![s(2)]));
    let queries: Vec<Query> = (0..4).map(|id| Query::Ty(s(id))).collect();
    every_order("early-failure", &early, &queries);

    // A ring through all four guarded kinds: struct S -> enum E -> entry
    // ty.0 (an `Array` element) -> declared tuple ty.0 -> S, entered also
    // through `Refine(ty.0)` (ty.1) and the inline tuple.
    let mut mixed = x86_64("four-kinds");
    mixed.types.push(Ty::Tuple(vec![s(0)])); // ty.0
    mixed.types.push(Ty::Refine(TyId::new(0), PredId::new(0))); // ty.1
    mixed.add_struct(strukt(0, vec![Ty::Enum(EnumId::new(0))]));
    mixed.enums.push(EnumDef::new(
        EnumId::new(0),
        "E",
        vec![EnumVariant {
            name: "V".into(),
            fields: vec![Ty::Array(TyId::new(0), 2)],
            field_names: Vec::new(),
        }],
    ));
    mixed.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type: TyId::new(0),
        size: 8,
        align: 8,
        field_offsets: vec![0],
    });
    let queries = vec![
        Query::Ty(s(0)),
        Query::Ty(Ty::Enum(EnumId::new(0))),
        Query::Enum(EnumId::new(0)),
        Query::Ty(Ty::Array(TyId::new(0), 2)),
        Query::Ty(mixed.types[0].clone()),
        Query::Ty(mixed.types[1].clone()),
        Query::TupleLayouts,
    ];
    assert_eq!(every_order("four-kinds", &mixed, &queries), 5040);
    // The four re-entry refusals all occur.
    let names: std::collections::BTreeSet<_> = queries
        .iter()
        .filter_map(
            |query| match ask_oracle(&mixed, &oracle::least_fixpoint(&mixed), query) {
                Answer::Ty(Err(error))
                | Answer::Enum(Err(error))
                | Answer::TupleLayouts(Err(error)) => Some(error_name(&error)),
                _ => None,
            },
        )
        .collect();
    for name in [
        "StructLayoutIncoherent",
        "EnumLayoutUnavailable",
        "TyLayoutCycle",
        "TupleLayoutIncoherent",
    ] {
        assert!(names.contains(name), "{name}: {names:?}");
    }

    // Wire v58: a ring through a DECLARED closure frame. Closure 0 captures
    // struct S0 by value, S0 holds closure 0: entered at the closure, at S0,
    // at the tail struct S1 -> S0 or by the row check, the recursion names the re-entered node and so must every
    // order of the table. Closure 1 is coherent and outside the ring (a
    // reordered frame: its second capture at offset 0), closure 2 captures
    // ITSELF, and closure 3 has a frame one byte short of its capture.
    let mut closures = x86_64("closure-ring");
    closures.add_struct(strukt(0, vec![Ty::U64, Ty::Closure(ClosureTyId::new(0))]));
    closures.add_struct(strukt(1, vec![s(0)]));
    for captures in [
        vec![s(0)],
        vec![Ty::U32, Ty::U64],
        vec![Ty::Closure(ClosureTyId::new(2))],
        vec![Ty::U64],
    ] {
        closures.closure_types.push(ClosureTy {
            func: FuncTyId::new(0),
            captures,
        });
    }
    for (closure, size, capture_offsets) in [
        (0, 16, vec![0]),
        (1, 16, vec![8, 0]),
        (2, 8, vec![0]),
        (3, 7, vec![0]),
    ] {
        closures.closure_layouts.push(ClosureLayoutDescriptor {
            origin: None,
            closure: ClosureTyId::new(closure),
            size,
            align: if closure == 3 { 1 } else { 8 },
            capture_offsets,
        });
    }
    let closure = |id: u32| Ty::Closure(ClosureTyId::new(id));
    let queries = vec![
        Query::Ty(closure(0)),
        Query::Ty(s(0)),
        Query::Ty(s(1)),
        Query::Ty(closure(1)),
        Query::Ty(closure(2)),
        Query::Ty(closure(3)),
        Query::ClosureLayouts,
    ];
    assert_eq!(every_order("closure-ring", &closures, &queries), 5040);
    let fixpoint = oracle::least_fixpoint(&closures);
    // The reordered frame lays out; the ring, the self-capture and the short
    // frame are each refused by name.
    assert!(matches!(
        ask_oracle(&closures, &fixpoint, &Query::Ty(closure(1))),
        Answer::Ty(Ok(_))
    ));
    for (query, name) in [
        (Query::Ty(closure(0)), "ClosureLayoutIncoherent"),
        (Query::Ty(s(0)), "StructLayoutIncoherent"),
        (Query::Ty(closure(2)), "ClosureLayoutIncoherent"),
        (Query::Ty(closure(3)), "ClosureLayoutIncoherent"),
    ] {
        let answer = ask_oracle(&closures, &fixpoint, &query);
        assert_eq!(
            answer.error().map(error_name),
            Some(name),
            "{query:?}: {answer:?}"
        );
    }
    // A duplicate row for the ring's closure refuses every closure query
    // that reaches the scan past it, in every order, as the scan did.
    let mut duplicated = closures.clone();
    duplicated
        .closure_layouts
        .insert(1, duplicated.closure_layouts[0].clone());
    every_order("closure-duplicate-row", &duplicated, &queries);
    // A row naming no closure type refuses every closure query reached
    // after it, and none before.
    let mut stray = closures.clone();
    stray.closure_layouts.insert(
        2,
        ClosureLayoutDescriptor {
            origin: None,
            closure: ClosureTyId::new(9),
            size: 8,
            align: 8,
            capture_offsets: vec![0],
        },
    );
    every_order("closure-stray-row", &stray, &queries);
    // No target: every declared frame is `ClosureLayoutTargetMissing`.
    let mut targetless = closures.clone();
    targetless.target_info = None;
    every_order("closure-no-target", &targetless, &queries);
}

// ---------------------------------------------------------------------------
// Shared sub-types and deep chains: linear work, no recursion
// ---------------------------------------------------------------------------

/// `P{k+1} = {Pk, Pk}`: zero-sized, so every depth has a layout; the
/// recursion walked 2^k paths, the table lays out k + 1 structs.
fn doubling(depth: u32) -> Module {
    let mut module = x86_64("doubling");
    module.add_struct(StructDef {
        id: StructId::new(0),
        name: "P0".into(),
        fields: Vec::new(),
        size: Some(0),
        align: Some(1),
        repr: StructRepr::C,
        origin: None,
    });
    for k in 1..=depth {
        module.add_struct(StructDef {
            id: StructId::new(k),
            name: format!("P{k}"),
            fields: (0..2)
                .map(|index| FieldDef {
                    name: format!("f{index}"),
                    ty: s(k - 1),
                    offset: Some(0),
                })
                .collect(),
            size: Some(0),
            align: Some(1),
            repr: StructRepr::C,
            origin: None,
        });
    }
    module
}

#[test]
fn shared_sub_types_are_laid_out_once() {
    // Against the oracle while it is still cheap (2^14 paths).
    let small = doubling(14);
    let queries: Vec<Query> = (0..=14).map(|k| Query::Ty(s(k))).collect();
    let order: Vec<usize> = (0..queries.len()).rev().collect();
    compare(
        "doubling",
        &small,
        &queries,
        &[order],
        &mut Census::default(),
    );

    // The work bound FIRST, at a depth where a broken memo (2^21 steps)
    // still finishes in about a second: so a regression fails this
    // assertion instead of starting the 10^5-deep walk below, which a broken
    // memo would never finish.
    let module = doubling(20);
    let table = module.layout_table();
    table.ty_layout(&s(20)).expect("P_20 is a ZST");
    let stats = table.stats();
    assert_eq!(stats.nodes, 21, "{stats:?}");
    assert!(stats.steps <= 3 * 40 + 4, "{stats:?}");
    assert!(stats.definitions_indexed <= 21, "{stats:?}");

    // Far past where the recursion ended (2^20 paths took 172 ms; 2^64 never
    // finishes): one node per struct, a bounded number of steps per field.
    let depth = 100_000;
    let module = doubling(depth);
    let table = module.layout_table();
    let layout = table.ty_layout(&s(depth)).expect("P_k is a ZST");
    assert_eq!((layout.size_bits, layout.align_bits), (0, Some(8)));
    let stats = table.stats();
    let fields = 2 * u64::from(depth);
    assert_eq!(stats.nodes, depth as usize + 1);
    assert!(stats.steps <= 3 * fields + 4, "{stats:?}");
    // Every other root is a lookup.
    for k in (0..depth).step_by(997) {
        table.ty_layout(&s(k)).expect("laid out");
    }
    assert_eq!(table.stats().nodes, depth as usize + 1);
}

/// Each struct holds the previous one; each enum's one variant holds the
/// previous enum; and the type table alternates an array of the previous
/// entry with a declared tuple holding an array of the previous entry.
fn chains(depth: u32) -> Module {
    let mut module = x86_64("chains");
    module.add_struct(strukt(0, vec![Ty::U64]));
    for k in 1..depth {
        module.add_struct(strukt(k, vec![s(k - 1)]));
    }
    module.enums.push(EnumDef::new(
        EnumId::new(0),
        "E0",
        vec![EnumVariant {
            name: "V".into(),
            fields: vec![Ty::U8],
            field_names: Vec::new(),
        }],
    ));
    for k in 1..depth {
        module.enums.push(EnumDef::new(
            EnumId::new(k),
            format!("E{k}"),
            vec![EnumVariant {
                name: "V".into(),
                fields: vec![Ty::Enum(EnumId::new(k - 1))],
                field_names: Vec::new(),
            }],
        ));
    }
    // ty.0 = u8; ty.2k+1 = [ty.2k; 1]; ty.2k+2 = (ty.2k+1,) declared.
    module.types.push(Ty::U8);
    for _ in 0..depth {
        let array = module.types.len() as u32;
        module.types.push(Ty::Array(TyId::new(array - 1), 1));
        let tuple = module.types.len() as u32;
        module
            .types
            .push(Ty::Tuple(vec![Ty::Array(TyId::new(array), 1)]));
        module.tuple_layouts.push(TupleLayoutDescriptor {
            tuple_type: TyId::new(tuple),
            size: 1,
            align: 1,
            field_offsets: vec![0],
        });
    }
    module
}

#[test]
fn hundred_thousand_deep_chains_lay_out_on_a_small_stack() {
    // The recursion overflowed a 2 MiB stack at depth 4096. The table walks
    // on the heap, so 256 KiB is plenty at any depth.
    let depth = 100_000u32;
    let module = chains(depth);
    let worker = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(move || {
            let table = module.layout_table();
            let top = depth - 1;
            let layout = table.ty_layout(&s(top)).expect("struct chain");
            assert_eq!(layout.size_bits, 64);
            let shape = table.enum_layout(EnumId::new(top)).expect("enum chain");
            // Each level adds a one-byte tag in front of the previous enum.
            assert_eq!(shape.size_bits, 8 * (u64::from(depth) + 1));
            let last = module.types.len() - 1;
            let tuple = table.ty_layout(&module.types[last]).expect("tuple chain");
            assert_eq!(tuple.size_bits, 8);
            let array = table
                .ty_layout(&Ty::Array(TyId::new(last as u32 - 1), 3))
                .expect("array chain");
            assert_eq!(array.size_bits, 24);
            // One node per struct, enum, table entry (the arrays' elements:
            // every array and every tuple entry) and tuple row; a bounded
            // number of steps for each of their fields.
            let stats = table.stats();
            let nodes = 5 * depth as usize;
            assert!(stats.nodes <= nodes + 2, "{stats:?}");
            assert!(stats.steps <= 3 * nodes as u64 + 16, "{stats:?}");
            // The id indexes read each row at most once: a lookup that slid
            // back to a scan per question would read about depth^2 / 2.
            assert!(
                stats.definitions_indexed <= module.structs.len() + module.enums.len(),
                "{stats:?}"
            );
            assert!(
                stats.tuple_rows_indexed <= module.tuple_layouts.len(),
                "{stats:?}"
            );
            assert_eq!(table.validate_tuple_layouts(), Ok(()));
            assert_eq!(table.stats().tuple_rows_indexed, module.tuple_layouts.len());
            assert_eq!(module.validate_tuple_layouts(), Ok(()));
        })
        .expect("spawn");
    worker.join().expect("no stack overflow");
}

// ---------------------------------------------------------------------------
// The niche rule over a wide or deep uninhabited payload
// ---------------------------------------------------------------------------

#[test]
fn uninhabited_direct_profiles_match_independent_oracle_and_keep_physical_padding() {
    use trust_ir::{FieldStorageLayout, UninhabitedVariantLayout};
    let mut module = x86_64("uninhabited_direct_oracle");
    module.add_enum(EnumDef::new(EnumId::new(0), "Infallible", vec![]));
    let wide = module.add_type(Ty::U128).unwrap();
    let dead = Ty::Tuple(vec![Ty::Enum(EnumId::new(0)), Ty::Array(wide, 4096)]);
    let row = |name: &str, fields| EnumVariant {
        name: name.into(),
        fields,
        field_names: vec![],
    };
    let mut definition = EnumDef::new(
        EnumId::new(1),
        "Nested",
        vec![row("Dead", vec![dead.clone()]), row("Live", vec![Ty::U32])],
    )
    .with_repr(EnumTagRepr::U32);
    definition.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::DirectWithUninhabited {
            tag_offset: 0,
            variants: vec![UninhabitedVariantLayout {
                variant: 0,
                size: 65_552,
                align: 16,
                fields: vec![FieldStorageLayout {
                    size: 65_536,
                    align: 16,
                }],
            }],
        },
        size: 65_552,
        align: 16,
        variant_field_offsets: vec![vec![16], vec![4]],
    });
    module.add_enum(definition);
    let queries = [
        Query::Enum(EnumId::new(1)),
        Query::Ty(Ty::Enum(EnumId::new(1))),
        Query::Uninhabited(dead),
        Query::Enum(EnumId::new(0)),
    ];
    let orders = vec![vec![0, 1, 2, 3], vec![3, 2, 1, 0]];
    let mut census = Census::default();
    compare(
        "physical dead-row image",
        &module,
        &queries,
        &orders,
        &mut census,
    );
    let shape = module.enum_layout_shape(EnumId::new(1)).unwrap();
    assert_eq!((shape.size_bits, shape.align_bits), (65_552 * 8, 16 * 8));
    assert_eq!(
        (shape.payload_size_bits, shape.payload_offset_bits),
        (65_536 * 8, 16 * 8)
    );
    for mutation in 0..10 {
        let mut changed = module.clone();
        let descriptor = changed.enums[1].layout.as_mut().unwrap();
        let EnumTagEncoding::DirectWithUninhabited { variants, .. } = &mut descriptor.encoding
        else {
            unreachable!()
        };
        match mutation {
            0 => variants.clear(),
            1 => variants[0].variant = 1,
            2 => variants.push(variants[0].clone()),
            3 => variants[0].fields[0].align = 0,
            4 => variants[0].fields[0].size = 65_535,
            5 => descriptor.variant_field_offsets[0][0] = 0,
            6 => variants[0].fields[0].size = 65_552,
            7 => variants[0].size = 65_536,
            8 => changed.enums[1].variants[0]
                .fields
                .push(Ty::Struct(StructId::new(404))),
            9 => changed.enums[1].variants[0].fields = vec![Ty::Unit],
            _ => unreachable!(),
        }
        compare(
            &format!("uninhabited Direct refusal {mutation}"),
            &changed,
            &queries,
            &orders,
            &mut census,
        );
        assert!(
            changed.enum_layout_shape(EnumId::new(1)).is_err(),
            "mutation {mutation}"
        );
    }
}

/// `Z = enum { V(!) }`, declared untagged and zero-sized: it lays out, and it
/// is uninhabited.
fn void_enum(id: u32) -> EnumDef {
    let mut def = EnumDef::new(
        EnumId::new(id),
        "Z",
        vec![EnumVariant {
            name: "V".into(),
            fields: vec![Ty::Never],
            field_names: Vec::new(),
        }],
    );
    def.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Untagged,
        size: 0,
        align: 1,
        variant_field_offsets: vec![vec![0]],
    });
    def
}

/// `E = enum { A(u8), B(payload) }` with a one-byte niche in `A` that
/// encodes only `A`: it lays out exactly when `B` is uninhabited.
fn niche_enum(id: u32, payload: Ty, payload_size: u64) -> EnumDef {
    let variant = |name: &str, ty: Ty| EnumVariant {
        name: name.into(),
        fields: vec![ty],
        field_names: Vec::new(),
    };
    let mut def = EnumDef::new(
        EnumId::new(id),
        "E",
        vec![variant("A", Ty::U8), variant("B", payload)],
    );
    def.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Niche {
            untagged_variant: 0,
            niche_variants_start: 0,
            niche_variants_end: 0,
            niche_start: 0,
            niche_offset: 0,
            niche_ty: EnumTagRepr::U8,
        },
        size: payload_size.max(1),
        align: 1,
        variant_field_offsets: vec![vec![0], vec![0]],
    });
    def
}

/// `S0 = { S1, .., Sn, Z }` with `Si = { u8 }`: uninhabited through its last
/// field, after `n` inhabited ones; `E` niches over it.
fn wide_niche(n: u32) -> Module {
    let mut module = x86_64("wide-niche");
    let byte = |id: u32| StructDef {
        id: StructId::new(id),
        name: format!("S{id}"),
        fields: vec![FieldDef {
            name: "b".into(),
            ty: Ty::U8,
            offset: Some(0),
        }],
        size: Some(1),
        align: Some(1),
        repr: StructRepr::C,
        origin: None,
    };
    let mut fields: Vec<FieldDef> = (1..=n)
        .map(|i| FieldDef {
            name: format!("f{i}"),
            ty: s(i),
            offset: Some(u64::from(i - 1)),
        })
        .collect();
    fields.push(FieldDef {
        name: "z".into(),
        ty: Ty::Enum(EnumId::new(0)),
        offset: Some(0),
    });
    module.add_struct(StructDef {
        id: StructId::new(0),
        name: "S0".into(),
        fields,
        size: Some(u64::from(n)),
        align: Some(1),
        repr: StructRepr::C,
        origin: None,
    });
    for i in 1..=n {
        module.add_struct(byte(i));
    }
    module.enums.push(void_enum(0));
    module.enums.push(niche_enum(1, s(0), u64::from(n)));
    module
}

/// `S0 -> S1 -> .. -> S(n-1) -> Z`, all zero-sized; `E` niches over `S0`.
fn deep_niche(n: u32) -> Module {
    let mut module = x86_64("deep-niche");
    for i in 0..n {
        let ty = if i + 1 < n {
            s(i + 1)
        } else {
            Ty::Enum(EnumId::new(0))
        };
        module.add_struct(StructDef {
            id: StructId::new(i),
            name: format!("S{i}"),
            fields: vec![FieldDef {
                name: "f".into(),
                ty,
                offset: Some(0),
            }],
            size: Some(0),
            align: Some(1),
            repr: StructRepr::C,
            origin: None,
        });
    }
    module.enums.push(void_enum(0));
    module.enums.push(niche_enum(1, s(0), 0));
    module
}

#[test]
fn a_niche_over_a_wide_uninhabited_payload_is_decided_in_linear_work() {
    // Against the oracle while it is small.
    for n in [1, 2, 7, 64] {
        let module = wide_niche(n);
        let queries = module_queries(&module);
        let orders = orders(&mut Rng(u64::from(n)), queries.len(), 2);
        compare(
            "wide niche",
            &module,
            &queries,
            &orders,
            &mut Census::default(),
        );
    }
    // The recursion re-scanned the struct list at every struct it entered
    // under a fresh guard per variant: about 5x per doubling, 2.66 s at
    // 2^16. The memo decides each node once.
    let n = 1u32 << 16;
    let module = wide_niche(n);
    let table = module.layout_table();
    let payload = table.ty_layout(&s(0)).expect("S0 lays out");
    assert_eq!(payload.size_bits, 8 * u64::from(n));
    let before = table.stats();
    assert_eq!(before.inhabitedness_nodes, 0, "{before:?}");
    let layout = table
        .ty_layout(&Ty::Enum(EnumId::new(1)))
        .expect("E lays out: B is uninhabited, so the niche need not encode it");
    assert_eq!(layout.size_bits, 8 * u64::from(n));
    let stats = table.stats();
    let n = n as usize;
    assert!(stats.inhabitedness_nodes <= n + 4, "{stats:?}");
    assert!(stats.inhabitedness_steps <= 5 * n as u64 + 32, "{stats:?}");
    assert!(
        stats.inhabitedness_rows_indexed
            <= module.structs.len() + module.enums.len() + module.records.len(),
        "{stats:?}"
    );
    // The layout walk itself added a handful of steps for the enum.
    assert!(
        stats.steps <= before.steps + 16,
        "{stats:?} after {before:?}"
    );
    // Asking again, or asking the variant, reads the memo.
    assert!(table.variant_is_uninhabited(&module.enums[1].variants[1]));
    assert!(!table.variant_is_uninhabited(&module.enums[1].variants[0]));
    assert_eq!(table.stats().inhabitedness_nodes, stats.inhabitedness_nodes);
}

#[test]
fn a_niche_over_a_deep_uninhabited_payload_is_decided_on_a_small_stack() {
    for n in [1, 2, 9, 64] {
        let module = deep_niche(n);
        let queries = module_queries(&module);
        let orders = orders(&mut Rng(u64::from(n)), queries.len(), 2);
        compare(
            "deep niche",
            &module,
            &queries,
            &orders,
            &mut Census::default(),
        );
    }
    // The recursion overflowed a 256 KiB stack at depth 4000, and an 8 MiB
    // one at 10^5. The memo decides on the heap.
    let n = 100_000u32;
    let worker = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(move || {
            let module = deep_niche(n);
            let table = module.layout_table();
            let layout = table
                .ty_layout(&Ty::Enum(EnumId::new(1)))
                .expect("E lays out: B is uninhabited");
            assert_eq!(layout.size_bits, 8);
            let stats = table.stats();
            let n = n as usize;
            assert!(stats.nodes <= n + 3, "{stats:?}");
            assert!(stats.inhabitedness_nodes <= n + 3, "{stats:?}");
            assert!(stats.inhabitedness_steps <= 5 * n as u64 + 32, "{stats:?}");
            // The `Module` methods, a fresh memo each, on the same stack.
            assert!(module.ty_is_uninhabited(&s(0)));
            assert!(module.variant_is_uninhabited(&module.enums[1].variants[1]));
            assert_eq!(
                module.niche_unencoded_inhabited_variant(&module.enums[1], 0, 0, 0),
                None
            );
            assert!(module.enum_layout_shape(EnumId::new(1)).is_ok());
        })
        .expect("spawn");
    worker.join().expect("no stack overflow");
}

// ---------------------------------------------------------------------------
// Inhabitedness: the least fixpoint, and the recursion it replaced
// ---------------------------------------------------------------------------

/// The nodes a value of `ty` holds by value, for inhabitedness (the edges
/// the rules read).
fn literal_nodes(module: &Module, ty: &Ty, out: &mut Vec<oracle::INode>) {
    match ty {
        Ty::Tuple(elems) => {
            for elem in elems {
                literal_nodes(module, elem, out);
            }
        }
        Ty::Array(elem, len) => {
            if *len > 0 && module.ty(*elem).is_some() {
                out.push(oracle::INode::Entry(elem.as_usize()));
            }
        }
        Ty::Refine(base, _) => {
            if module.ty(*base).is_some() {
                out.push(oracle::INode::Entry(base.as_usize()));
            }
        }
        Ty::Struct(id) => out.push(oracle::INode::Struct(*id)),
        Ty::Record(id) => out.push(oracle::INode::Record(*id)),
        Ty::Enum(id) => out.push(oracle::INode::Enum(*id)),
        _ => {}
    }
}

fn successors(module: &Module, node: oracle::INode) -> Vec<oracle::INode> {
    let mut out = Vec::new();
    match node {
        oracle::INode::Entry(index) => literal_nodes(module, &module.types[index], &mut out),
        oracle::INode::Struct(id) => {
            for def in module.structs.iter().filter(|def| def.id == id) {
                for field in &def.fields {
                    literal_nodes(module, &field.ty, &mut out);
                }
            }
        }
        oracle::INode::Record(id) => {
            for def in module.records.iter().filter(|def| def.id == id) {
                for field in &def.fields {
                    literal_nodes(module, &field.ty, &mut out);
                }
            }
        }
        oracle::INode::Enum(id) => {
            for def in module.enums.iter().filter(|def| def.id == id) {
                for ty in def.variants.iter().flat_map(|variant| &variant.fields) {
                    literal_nodes(module, ty, &mut out);
                }
            }
        }
    }
    out
}

/// Does the inhabitedness graph reached from `roots` hold a cycle?
fn reach_is_cyclic(module: &Module, roots: &[oracle::INode]) -> bool {
    // 1 = on the path, 2 = done.
    fn visit(
        module: &Module,
        node: oracle::INode,
        colour: &mut BTreeMap<oracle::INode, u8>,
    ) -> bool {
        match colour.get(&node) {
            Some(1) => return true,
            Some(_) => return false,
            None => {}
        }
        colour.insert(node, 1);
        for next in successors(module, node) {
            if visit(module, next, colour) {
                return true;
            }
        }
        colour.insert(node, 2);
        false
    }
    let mut colour = BTreeMap::new();
    roots.iter().any(|root| visit(module, *root, &mut colour))
}

#[derive(Default, Debug)]
struct InhabitCensus {
    questions: usize,
    uninhabited: usize,
    acyclic: usize,
    /// Questions where the old recursion answered "inhabited" and the least
    /// fixpoint "uninhabited" (each on a cyclic reach).
    old_below: usize,
}

/// Every inhabitedness question of `module`, answered by the `Module`
/// methods, a shared table, the naive least fixpoint and the old recursion.
fn check_inhabitedness(label: &str, module: &Module, census: &mut InhabitCensus) {
    let fixpoint = oracle::least_fixpoint(module);
    let table = module.layout_table();
    let mut questions: Vec<(Vec<Ty>, String)> = Vec::new();
    let mut ty_question = |ty: Ty| questions.push((vec![ty.clone()], format!("{ty:?}")));
    for def in &module.structs {
        ty_question(Ty::Struct(def.id));
    }
    for def in &module.records {
        ty_question(Ty::Record(def.id));
    }
    for def in &module.enums {
        ty_question(Ty::Enum(def.id));
    }
    for (index, ty) in module.types.iter().enumerate() {
        ty_question(Ty::Refine(TyId::new(index as u32), PredId::new(0)));
        ty_question(ty.clone());
    }
    for (index, def) in module.enums.iter().enumerate() {
        for (variant_index, variant) in def.variants.iter().enumerate() {
            questions.push((
                variant.fields.clone(),
                format!("enum def {index} variant {variant_index}"),
            ));
        }
    }
    for (tys, what) in questions {
        let variant = EnumVariant {
            name: "Q".into(),
            fields: tys.clone(),
            field_names: Vec::new(),
        };
        let least = fixpoint.variant_is_uninhabited(&variant);
        assert_eq!(
            module.variant_is_uninhabited(&variant),
            least,
            "{label}: Module, {what}"
        );
        assert_eq!(
            table.variant_is_uninhabited(&variant),
            least,
            "{label}: table, {what}"
        );
        if let [ty] = tys.as_slice() {
            assert_eq!(module.ty_is_uninhabited(ty), least, "{label}: {what}");
            assert_eq!(table.ty_is_uninhabited(ty), least, "{label}: {what}");
        }
        let old = oracle::old_variant_is_uninhabited(module, &variant);
        // Never above the least fixpoint: every "uninhabited" the recursion
        // said, a finite derivation says too.
        assert!(!old || least, "{label}: old above the fixpoint, {what}");
        let mut roots = Vec::new();
        for ty in &tys {
            literal_nodes(module, ty, &mut roots);
        }
        let cyclic = reach_is_cyclic(module, &roots);
        if !cyclic {
            census.acyclic += 1;
            assert_eq!(old, least, "{label}: acyclic reach, {what}");
        }
        if old != least {
            assert!(cyclic, "{label}: {what}");
            census.old_below += 1;
        }
        census.questions += 1;
        census.uninhabited += usize::from(least);
    }
}

#[test]
fn inhabitedness_is_the_least_fixpoint_and_the_old_recursion_where_acyclic() {
    let mut census = InhabitCensus::default();
    for seed in 0..6_000u64 {
        let module = random_module(seed);
        check_inhabitedness(&format!("seed {seed}"), &module, &mut census);
    }
    for module in [wide_niche(9), deep_niche(9), order_dependent()] {
        check_inhabitedness(&module.name.clone(), &module, &mut census);
    }
    eprintln!("inhabitedness: {census:?}");
    assert!(census.uninhabited >= 1_000, "{census:?}");
    assert!(census.acyclic >= 10_000, "{census:?}");
    // At least the two order-dependent questions of `order_dependent` (its
    // enum, and its enum's variant): the random graphs rarely meet one.
    assert!(census.old_below >= 2, "{census:?}");
}

/// Records `X = { y: Y, n: ! }` and `Y = { x: X }` (a by-value cycle the
/// validator refuses; an unvalidated module can still carry it), `G = enum
/// { V1(X), V2(u8) }`, and `E = enum { V(G, Y) }`.
fn order_dependent() -> Module {
    let mut module = x86_64("order-dependent");
    let record = |id: u32, fields: Vec<Ty>| RecordDef {
        id: RecordId::new(id),
        name: format!("R{id}"),
        fields: fields
            .into_iter()
            .enumerate()
            .map(|(index, ty)| FieldDef {
                name: format!("f{index}"),
                ty,
                offset: None,
            })
            .collect(),
    };
    let variant = |fields: Vec<Ty>| EnumVariant {
        name: "V".into(),
        fields,
        field_names: Vec::new(),
    };
    module
        .records
        .push(record(0, vec![Ty::Record(RecordId::new(1)), Ty::Never]));
    module
        .records
        .push(record(1, vec![Ty::Record(RecordId::new(0))]));
    module.enums.push(EnumDef::new(
        EnumId::new(0),
        "G",
        vec![
            variant(vec![Ty::Record(RecordId::new(0))]),
            variant(vec![Ty::U8]),
        ],
    ));
    module.enums.push(EnumDef::new(
        EnumId::new(1),
        "E",
        vec![variant(vec![
            Ty::Enum(EnumId::new(0)),
            Ty::Record(RecordId::new(1)),
        ])],
    ));
    module
}

#[test]
fn the_old_recursion_depended_on_the_order_it_met_a_cycle() {
    let module = order_dependent();
    let y = Ty::Record(RecordId::new(1));
    let e_variant = &module.enums[1].variants[0];
    // Asked alone, Y holds an X, which holds a `!`: no value.
    assert!(oracle::old_ty_is_uninhabited(&module, &y));
    // Asked after G, the recursion had memoized Y "inhabited" while X was on
    // its path, so the same Y, and E's variant holding it, came out inhabited.
    assert!(!oracle::old_variant_is_uninhabited(&module, e_variant));
    assert!(!oracle::old_ty_is_uninhabited(
        &module,
        &Ty::Enum(EnumId::new(1))
    ));
    // The least fixpoint answers the same from everywhere.
    let table = module.layout_table();
    assert!(table.variant_is_uninhabited(e_variant));
    assert!(table.ty_is_uninhabited(&y));
    assert!(module.variant_is_uninhabited(e_variant));
    assert!(module.ty_is_uninhabited(&Ty::Enum(EnumId::new(1))));
    assert!(!module.ty_is_uninhabited(&Ty::Enum(EnumId::new(0))));
    // A cycle that derives nothing stays inhabited.
    let mut ring = x86_64("ring");
    ring.records.push(RecordDef {
        id: RecordId::new(0),
        name: "R".into(),
        fields: vec![FieldDef {
            name: "r".into(),
            ty: Ty::Record(RecordId::new(0)),
            offset: None,
        }],
    });
    assert!(!ring.ty_is_uninhabited(&Ty::Record(RecordId::new(0))));
}

// ---------------------------------------------------------------------------
// One table across threads, and a memo lent back
// ---------------------------------------------------------------------------

#[test]
fn a_table_shared_by_threads_answers_as_the_recursion_did() {
    fn assert_sync<T: Sync + Send>() {}
    assert_sync::<LayoutTable<'static>>();
    let mut rng = Rng(0x7ead);
    for seed in 0..400u64 {
        let module = random_module(seed);
        let queries = module_queries(&module);
        let fixpoint = oracle::least_fixpoint(&module);
        let want: Vec<Answer> = queries
            .iter()
            .map(|query| ask_oracle(&module, &fixpoint, query))
            .collect();
        let orders = orders(&mut rng, queries.len(), 4);
        let table = LayoutTable::new(&module);
        std::thread::scope(|scope| {
            for order in &orders {
                let (table, queries, want) = (&table, &queries, &want);
                scope.spawn(move || {
                    for &index in order {
                        assert_eq!(
                            ask_table(table, &queries[index]),
                            want[index],
                            "seed {seed}: {:?}",
                            queries[index]
                        );
                    }
                });
            }
        });
    }
}

#[test]
fn a_lent_memo_answers_as_a_fresh_table() {
    let mut rng = Rng(0x1e47);
    for seed in 0..400u64 {
        let module = random_module(seed);
        let queries = module_queries(&module);
        let fixpoint = oracle::least_fixpoint(&module);
        let order = rng.permutation(queries.len());
        // Lend the memo back between every two questions.
        let mut memo = LayoutTable::new(&module).into_memo();
        for &index in &order {
            let table = LayoutTable::with_memo(&module, memo);
            assert_eq!(
                ask_table(&table, &queries[index]),
                ask_oracle(&module, &fixpoint, &queries[index]),
                "seed {seed}: {:?}",
                queries[index]
            );
            memo = table.into_memo();
        }
        // A memo lent to a module whose tables changed length is dropped: the
        // answers are the new module's.
        let mut grown = module.clone();
        grown.add_struct(strukt(grown.structs.len() as u32 + 1000, vec![Ty::U64]));
        grown.types.push(Ty::U8);
        let table = LayoutTable::with_memo(&grown, memo);
        assert_eq!(table.stats().nodes, 0, "seed {seed}");
        let fixpoint = oracle::least_fixpoint(&grown);
        for query in module_queries(&grown) {
            assert_eq!(
                ask_table(&table, &query),
                ask_oracle(&grown, &fixpoint, &query),
                "seed {seed}, grown: {query:?}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// The discriminant set, linear now
// ---------------------------------------------------------------------------

#[test]
fn effective_discriminants_answer_as_the_quadratic_scan_did() {
    let mut rng = Rng(0xd15c);
    for _ in 0..20_000 {
        let variants = rng.below(9) as usize;
        let mut def = EnumDef::new(
            EnumId::new(0),
            "E",
            (0..variants)
                .map(|index| EnumVariant {
                    name: format!("V{index}"),
                    fields: Vec::new(),
                    field_names: Vec::new(),
                })
                .collect(),
        );
        def.discriminants = (0..rng.below(variants as u64 + 2))
            .map(|_| {
                rng.chance(50).then(|| match rng.below(10) {
                    0 => i128::MAX,
                    1 => i128::MIN,
                    _ => rng.below(12) as i128 - 4,
                })
            })
            .collect();
        if rng.chance(30) {
            def.repr =
                Some([EnumTagRepr::U8, EnumTagRepr::I8, EnumTagRepr::U128][rng.below(3) as usize]);
        }
        assert_eq!(
            def.effective_discriminants(),
            oracle::effective_discriminants(&def),
            "{def:?}"
        );
        assert_eq!(
            def.canonical_tag_repr(),
            oracle::canonical_tag_repr(&def),
            "{def:?}"
        );
    }
}

/// Item storage is authenticated by original declaration identity, not the
/// pointer-size scalar table or by substituting Unit in the oracle.
#[test]
fn fn_item_layout_matches_independent_sparse_header_oracle() {
    use trust_ir::{BlockId, FuncId, FuncTy, Function, TyLayoutKind, TyShape};
    for selected_target in [
        None,
        Some(TargetInfo {
            triple: "wasm32-unknown-unknown".into(),
            pointer_size: 4,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: Default::default(),
        }),
        x86_64("explicit64").target_info,
    ] {
        let mut module = Module::new("independent nominal item layout");
        module.target_info = selected_target;
        let signature = module
            .add_func_type(FuncTy::unrecorded(vec![], vec![], false))
            .unwrap();
        for id in [11, 53] {
            // A genuine bodyless declaration suffices for storage identity;
            // this query does not grant a license to execute that body.
            module.functions.push(Function::new(
                FuncId::new(id),
                format!("item_{id}"),
                signature,
                BlockId::new(0),
            ));
        }
        let queries = [
            Query::Ty(Ty::FnItem(FuncId::new(11))),
            Query::Ty(Ty::FnItem(FuncId::new(53))),
        ];
        let orders = [vec![0, 1], vec![1, 0]];
        let expected = TyLayoutShape {
            size_bits: 0,
            align_bits: Some(8),
            kind: TyLayoutKind::FnItem,
        };
        for ty in [Ty::FnItem(FuncId::new(11)), Ty::FnItem(FuncId::new(53))] {
            assert_eq!(oracle::ty_layout_shape(&module, &ty), Ok(expected.clone()));
            assert_eq!(module.ty_layout_shape(&ty), Ok(expected.clone()));
        }
        compare("items", &module, &queries, &orders, &mut Census::default());
        module.functions.swap(0, 1);
        compare(
            "reordered items",
            &module,
            &queries,
            &orders,
            &mut Census::default(),
        );

        let bad = Err(LayoutError::UnsupportedTyShape(TyShape::FnItem));
        for (label, invalid) in [
            ("missing", {
                let mut missing = module.clone();
                missing
                    .functions
                    .retain(|function| function.id != FuncId::new(11));
                missing
            }),
            ("ambiguous", {
                let mut ambiguous = module.clone();
                ambiguous.functions.push(ambiguous.functions[1].clone());
                ambiguous
            }),
            ("missing signature", {
                let mut missing_signature = module.clone();
                missing_signature.func_types.clear();
                missing_signature
            }),
        ] {
            let ty = Ty::FnItem(FuncId::new(11));
            assert_eq!(oracle::ty_layout_shape(&invalid, &ty), bad, "{label}");
            assert_eq!(invalid.ty_layout_shape(&ty), bad, "{label}");
            compare(
                label,
                &invalid,
                &[Query::Ty(ty)],
                &[vec![0]],
                &mut Census::default(),
            );
        }
    }
}

#[test]
fn single_inhabited_descriptors_match_independent_oracle() {
    let mut module = x86_64("single_inhabited_oracle");
    let huge = module.add_type(Ty::U128).unwrap();
    let variant = |name: &str, fields| EnumVariant {
        name: name.into(),
        fields,
        field_names: vec![],
    };
    let mut def = EnumDef::new(
        EnumId::new(0),
        "Selected",
        vec![
            variant("Before", vec![Ty::Never, Ty::Array(huge, u64::MAX)]),
            variant("Live", vec![Ty::U32]),
            variant("After", vec![Ty::Never]),
        ],
    )
    .with_discriminants(vec![Some(-5), Some(42), Some(100)]);
    def.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::SingleInhabited { variant: 1 },
        size: 4,
        align: 4,
        variant_field_offsets: vec![vec![], vec![0], vec![]],
    });
    module.add_enum(def);
    let queries = [
        Query::Enum(EnumId::new(0)),
        Query::Ty(Ty::Enum(EnumId::new(0))),
    ];
    let orders = vec![vec![0, 1], vec![1, 0]];
    let mut census = Census::default();
    compare(
        "selected index with omitted overflowing dead storage",
        &module,
        &queries,
        &orders,
        &mut census,
    );
    assert_eq!(
        module.enum_layout_shape(EnumId::new(0)).unwrap().size_bits,
        32
    );

    for mutation in 0..6 {
        let mut changed = module.clone();
        match mutation {
            0 => changed.enums[0].variants[0].fields = vec![Ty::Unit],
            1 => {
                changed.enums[0].layout.as_mut().unwrap().encoding =
                    EnumTagEncoding::SingleInhabited { variant: 3 }
            }
            2 => {
                changed.enums[0]
                    .layout
                    .as_mut()
                    .unwrap()
                    .variant_field_offsets[0] = vec![0, 0]
            }
            3 => changed.enums[0].variants[0]
                .fields
                .push(Ty::Struct(StructId::new(404))),
            4 => changed.enums[0].variants[0].fields = vec![Ty::Enum(EnumId::new(0))],
            5 => changed.enums[0].variants[1].fields = vec![Ty::Never],
            _ => unreachable!(),
        }
        compare(
            &format!("single inhabited refusal {mutation}"),
            &changed,
            &queries,
            &orders,
            &mut census,
        );
        assert!(
            changed.enum_layout_shape(EnumId::new(0)).is_err(),
            "mutation {mutation}"
        );
    }
}

fn single_item_reference_module() -> Module {
    use trust_ir::{BlockId, FuncId, FuncTy, Function};

    let mut module = x86_64("single_nominal_reference_oracle");
    let signature = module
        .add_func_type(FuncTy::unrecorded(vec![], vec![], false))
        .unwrap();
    module.functions.push(Function::new(
        FuncId::new(7),
        "actual_item",
        signature,
        BlockId::new(0),
    ));
    let mut def = EnumDef::new(
        EnumId::new(0),
        "Selected",
        vec![
            EnumVariant {
                name: "Dead".into(),
                fields: vec![Ty::Never, Ty::FnItem(FuncId::new(7))],
                field_names: vec![],
            },
            EnumVariant {
                name: "Live".into(),
                fields: vec![Ty::U32],
                field_names: vec![],
            },
        ],
    );
    def.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::SingleInhabited { variant: 1 },
        size: 4,
        align: 4,
        variant_field_offsets: vec![vec![], vec![0]],
    });
    module.enums.push(def);
    module
}

#[test]
fn single_inhabited_oracle_checks_nominal_items_even_without_storage() {
    use trust_ir::FuncId;

    let module = single_item_reference_module();
    let queries = [
        Query::Enum(EnumId::new(0)),
        Query::Ty(Ty::Enum(EnumId::new(0))),
    ];
    let orders = vec![vec![0, 1], vec![1, 0]];
    let mut census = Census::default();
    compare(
        "dead nominal item reference",
        &module,
        &queries,
        &orders,
        &mut census,
    );
    assert_eq!(
        module.enum_layout_shape(EnumId::new(0)).unwrap().size_bits,
        32
    );
    for mutation in 0..4 {
        let mut changed = module.clone();
        match mutation {
            0 => changed.functions.clear(),
            1 => changed.functions.push(changed.functions[0].clone()),
            2 => changed.functions[0].ty = FuncTyId::new(99),
            3 => {
                let missing = changed.add_type(Ty::FnItem(FuncId::new(99))).unwrap();
                changed.enums[0].variants[0].fields[1] = Ty::Array(missing, 0);
            }
            _ => unreachable!(),
        }
        compare(
            &format!("dead nominal item refusal {mutation}"),
            &changed,
            &queries,
            &orders,
            &mut census,
        );
        assert!(changed.enum_layout_shape(EnumId::new(0)).is_err());
    }
}

#[test]
fn single_inhabited_oracle_keeps_one_declaration_and_live_zero_storage() {
    let mut module = single_item_reference_module();
    module.enums[0].variants.remove(0);
    let descriptor = module.enums[0].layout.as_mut().unwrap();
    descriptor.encoding = EnumTagEncoding::SingleInhabited { variant: 0 };
    descriptor.variant_field_offsets.remove(0);
    let queries = [
        Query::Enum(EnumId::new(0)),
        Query::Ty(Ty::Enum(EnumId::new(0))),
    ];
    let orders = vec![vec![0, 1], vec![1, 0]];
    let mut census = Census::default();
    compare(
        "one declared live variant",
        &module,
        &queries,
        &orders,
        &mut census,
    );
    assert_eq!(
        module.enum_layout_shape(EnumId::new(0)).unwrap().size_bits,
        32
    );
    module.enums[0].variants[0].fields.clear();
    let descriptor = module.enums[0].layout.as_mut().unwrap();
    descriptor.size = 0;
    descriptor.align = 1;
    descriptor.variant_field_offsets[0].clear();
    compare(
        "one declared zero-storage variant",
        &module,
        &queries,
        &orders,
        &mut census,
    );
    assert_eq!(
        module.enum_layout_shape(EnumId::new(0)).unwrap().size_bits,
        0
    );
}
