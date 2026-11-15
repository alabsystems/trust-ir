// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The `pair` placement rule's ABI lane count (WS3.11, `validate`'s
//! `abi_lanes`): an explicit-stack walk that counts each struct and enum once
//! per pass, with a by-value cycle (a re-entered open node) as "no count".
//!
//! It replaced a recursion cut off at 16 levels (kept verbatim below as
//! [`capped`]). The cut-off refused a `pair` on a two-lane value wrapped in 17
//! newtypes, which rustc stamps `ScalarPair` at any depth; walked a shared
//! sub-type once per path; and scanned the struct or enum list at every level.
//! The count is now that recursion WITHOUT the cut-off ([`uncapped`]: the same
//! rules, a path guard for cycles, an overflow as no count), which the
//! validator's verdicts must equal on random type graphs; the cut-off
//! recursion may only have said "no count" where it differs.

use std::collections::BTreeSet;

use trust_ir::ty::{
    EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant, FatPtrKind, FieldDef,
    FuncTy, StructDef, StructRepr, Ty,
};
use trust_ir::value::{BlockId, EnumId, FuncTyId, RecordId, StructId, TyId};
use trust_ir::{Endianness, FuncId, Function, Module, ParamAttrs, PassMode, TargetInfo};
use trust_ir_build::validate::{ValidationError, validate_module};

// ---------------------------------------------------------------------------
// The oracles
// ---------------------------------------------------------------------------

// The new selector case is explicit; the old recursive rules below otherwise
// remain the oracle for their original representations.
fn selected_variant(module: &Module, def: &EnumDef, selected: u32) -> Option<usize> {
    let selected = selected as usize;
    if selected >= def.variants.len()
        || def
            .variants
            .iter()
            .enumerate()
            .any(|(index, item)| module.variant_is_uninhabited(item) == (index == selected))
    {
        None
    } else {
        Some(selected)
    }
}

fn is_closed_scalar_ty(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::Isize
            | Ty::Usize
            | Ty::Char
            | Ty::F16
            | Ty::F32
            | Ty::F64
            | Ty::Bool
            | Ty::Ptr
            | Ty::Unit
    )
}

/// The recursion before the memo, verbatim (with `module.ty_layout_shape`
/// for the scalar sizes), its 16-level cut-off included.
fn capped(module: &Module, ty: &Ty, depth: usize) -> Option<usize> {
    const ABI_LANES_MAX_DEPTH: usize = 16;
    if depth > ABI_LANES_MAX_DEPTH {
        return None;
    }
    let size_of = |ty: &Ty| module.ty_layout_shape(ty).ok().and_then(|s| s.size_bytes());
    let sum = |fields: &mut dyn Iterator<Item = &Ty>| -> Option<usize> {
        let mut lanes = 0usize;
        for field in fields {
            lanes += capped(module, field, depth + 1)?;
        }
        Some(lanes)
    };
    match ty {
        _ if is_closed_scalar_ty(ty) => Some(usize::from(size_of(ty)? != 0)),
        Ty::Ref(_) | Ty::RefMut(_) | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Rc(_) => Some(1),
        Ty::FatPtr(_) => Some(2),
        Ty::Tuple(fields) => sum(&mut fields.iter()),
        Ty::Struct(id) => {
            let def = module.structs.iter().find(|def| def.id == *id)?;
            sum(&mut def.fields.iter().map(|f| &f.ty))
        }
        Ty::Enum(id) => {
            let def = module.enums.iter().find(|def| def.id == *id)?;
            if def.variants.is_empty() {
                return None;
            }
            let variant_lanes = |index: usize| -> Option<usize> {
                sum(&mut def.variants.get(index)?.fields.iter())
            };
            match def.layout.as_ref().map(|layout| &layout.encoding) {
                Some(EnumTagEncoding::SingleInhabited { variant }) => {
                    variant_lanes(selected_variant(module, def, *variant)?)
                }
                Some(EnumTagEncoding::Untagged) => (def.variants.len() == 1)
                    .then(|| variant_lanes(0))
                    .flatten(),
                Some(EnumTagEncoding::Niche {
                    untagged_variant, ..
                }) => {
                    let dataful = *untagged_variant as usize;
                    for index in 0..def.variants.len() {
                        if index != dataful && variant_lanes(index)? != 0 {
                            return None;
                        }
                    }
                    variant_lanes(dataful)
                }
                Some(EnumTagEncoding::Direct { .. }) | None => {
                    let mut widest = 0usize;
                    for index in 0..def.variants.len() {
                        let lanes = variant_lanes(index)?;
                        if lanes > 1 {
                            return None;
                        }
                        widest = widest.max(lanes);
                    }
                    Some(1 + widest)
                }
            }
        }
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Open {
    Struct(StructId),
    Enum(EnumId),
}

/// The same rules with no cut-off: a struct or enum re-entered on its own
/// path is a cycle (no count), and a sum that does not fit is no count.
fn uncapped(module: &Module, ty: &Ty, path: &mut Vec<Open>) -> Option<usize> {
    let size_of = |ty: &Ty| module.ty_layout_shape(ty).ok().and_then(|s| s.size_bytes());
    fn sum<'a>(
        module: &Module,
        fields: impl Iterator<Item = &'a Ty>,
        path: &mut Vec<Open>,
    ) -> Option<usize> {
        let mut lanes = 0usize;
        for field in fields {
            lanes = lanes.checked_add(uncapped(module, field, path)?)?;
        }
        Some(lanes)
    }
    match ty {
        _ if is_closed_scalar_ty(ty) => Some(usize::from(size_of(ty)? != 0)),
        Ty::Ref(_) | Ty::RefMut(_) | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Rc(_) => Some(1),
        Ty::FatPtr(_) => Some(2),
        Ty::Tuple(fields) => sum(module, fields.iter(), path),
        Ty::Struct(id) => {
            let def = module.structs.iter().find(|def| def.id == *id)?;
            if path.contains(&Open::Struct(*id)) {
                return None;
            }
            path.push(Open::Struct(*id));
            let lanes = sum(module, def.fields.iter().map(|f| &f.ty), path);
            path.pop();
            lanes
        }
        Ty::Enum(id) => {
            let def = module.enums.iter().find(|def| def.id == *id)?;
            if def.variants.is_empty() {
                return None;
            }
            if path.contains(&Open::Enum(*id)) {
                return None;
            }
            path.push(Open::Enum(*id));
            let variant_lanes = |index: usize, path: &mut Vec<Open>| -> Option<usize> {
                sum(module, def.variants.get(index)?.fields.iter(), path)
            };
            let lanes = (|| match def.layout.as_ref().map(|layout| &layout.encoding) {
                Some(EnumTagEncoding::SingleInhabited { variant }) => {
                    variant_lanes(selected_variant(module, def, *variant)?, path)
                }
                Some(EnumTagEncoding::Untagged) => (def.variants.len() == 1)
                    .then(|| variant_lanes(0, path))
                    .flatten(),
                Some(EnumTagEncoding::Niche {
                    untagged_variant, ..
                }) => {
                    let dataful = *untagged_variant as usize;
                    for index in 0..def.variants.len() {
                        if index != dataful && variant_lanes(index, path)? != 0 {
                            return None;
                        }
                    }
                    variant_lanes(dataful, path)
                }
                Some(EnumTagEncoding::Direct { .. }) | None => {
                    let mut widest = 0usize;
                    for index in 0..def.variants.len() {
                        let lanes = variant_lanes(index, path)?;
                        if lanes > 1 {
                            return None;
                        }
                        widest = widest.max(lanes);
                    }
                    Some(1 + widest)
                }
            })();
            path.pop();
            lanes
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// The validator's verdict
// ---------------------------------------------------------------------------

fn target() -> TargetInfo {
    TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

/// Append one bodyless declaration per type, its one parameter claimed
/// `pair`; returns the declarations' function indices.
fn claim_pairs(module: &mut Module, types: &[Ty]) -> Vec<u32> {
    let mut ids = Vec::new();
    for ty in types {
        let sig = FuncTyId::new(module.func_types.len() as u32);
        module.func_types.push(FuncTy {
            params: vec![ty.clone()],
            returns: Vec::new(),
            abi: None,
            is_vararg: false,
        });
        let id = module.functions.len() as u32;
        let mut decl = Function::new(FuncId::new(id), format!("pair_{id}"), sig, BlockId::new(0));
        decl.attrs.params = vec![ParamAttrs {
            pass: Some(PassMode::Pair),
            ..ParamAttrs::default()
        }];
        module
            .try_add_function(decl)
            .expect("Module::try_add_function: test fixture");
        ids.push(id);
    }
    ids
}

/// The functions whose `pair` claim the validator refuses for its lanes.
fn refused_pairs(module: &Module) -> BTreeSet<u32> {
    validate_module(module)
        .into_iter()
        .filter_map(|error| match error {
            ValidationError::InvalidAbiSlotFact {
                function, detail, ..
            } if detail.contains("two-scalar-lane") => Some(function),
            _ => None,
        })
        .collect()
}

#[derive(Default, Debug)]
struct Census {
    admitted: usize,
    refused: usize,
    /// The cut-off recursion said "no count" where the rules give one.
    cut_off: usize,
}

/// Every claim's verdict is the uncapped rule's, and the cut-off recursion
/// differs from it only by saying "no count".
fn compare(label: &str, module: &Module, types: &[Ty], census: &mut Census) {
    let mut module = module.clone();
    let ids = claim_pairs(&mut module, types);
    let refused = refused_pairs(&module);
    for (ty, id) in types.iter().zip(ids) {
        let want = uncapped(&module, ty, &mut Vec::new());
        assert_eq!(
            refused.contains(&id),
            want != Some(2),
            "{label}: pair on {ty:?} (rule: {want:?})"
        );
        // Where the rule gives no count the cut-off gave none either (and on
        // a cycle it walks every path to its 16th level: not asked).
        if want.is_some() {
            let old = capped(&module, ty, 0);
            assert!(
                old == want || old.is_none(),
                "{label}: {ty:?}: cut-off {old:?}, rule {want:?}"
            );
            census.cut_off += usize::from(old != want);
        }
        if want == Some(2) {
            census.admitted += 1;
        } else {
            census.refused += 1;
        }
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
}

struct Gen {
    rng: Rng,
    structs: u32,
    enums: u32,
}

impl Gen {
    fn ty(&mut self, depth: u32) -> Ty {
        match self.rng.below(100) {
            0..=9 => Ty::U64,
            10..=14 => Ty::U32,
            15..=17 => Ty::Bool,
            18..=22 => Ty::Unit,
            23..=25 => Ty::Ptr,
            26..=27 => Ty::F64,
            28..=31 => Ty::Ref(Box::new(Ty::U8)),
            32..=33 => Ty::FatPtr(FatPtrKind::Str),
            34 => Ty::FatPtr(FatPtrKind::Slice(TyId::new(0))),
            35 => Ty::Array(TyId::new(0), 1),
            36 => Ty::Vector(Box::new(Ty::U8), 2),
            37 => Ty::Record(RecordId::new(0)),
            38..=62 => Ty::Struct(StructId::new(
                self.rng.below(u64::from(self.structs) + 1) as u32
            )),
            63..=82 => Ty::Enum(EnumId::new(self.rng.below(u64::from(self.enums) + 1) as u32)),
            83..=99 if depth > 0 => {
                let n = self.rng.below(4);
                Ty::Tuple((0..n).map(|_| self.ty(depth - 1)).collect())
            }
            _ => Ty::U8,
        }
    }

    fn fields(&mut self, max: u64) -> Vec<Ty> {
        let n = self.rng.below(max + 1);
        (0..n).map(|_| self.ty(1)).collect()
    }

    fn encoding(&mut self, variants: usize) -> Option<EnumLayoutDescriptor> {
        let encoding = match self.rng.below(4) {
            0 => return None,
            1 => EnumTagEncoding::Direct { tag_offset: 0 },
            2 => EnumTagEncoding::Untagged,
            _ => EnumTagEncoding::Niche {
                // Now and then past the variants.
                untagged_variant: self.rng.below(variants as u64 + 1) as u32,
                niche_variants_start: 0,
                niche_variants_end: 0,
                niche_start: 0,
                niche_offset: 0,
                niche_ty: EnumTagRepr::U8,
            },
        };
        Some(EnumLayoutDescriptor {
            encoding,
            size: 16,
            align: 8,
            variant_field_offsets: vec![Vec::new(); variants],
        })
    }
}

fn random_module(seed: u64) -> (Module, Vec<Ty>) {
    let mut rng = Rng(seed);
    let structs = 1 + rng.below(8) as u32;
    let enums = 1 + rng.below(6) as u32;
    let mut g = Gen {
        rng: Rng(seed ^ 0xab1_1a7e),
        structs,
        enums,
    };
    let mut module = Module::new("abi_lanes");
    module.target_info = Some(target());
    for index in 0..structs {
        // A duplicate id now and then: the first definition counts.
        let id = if index > 0 && g.rng.chance(8) {
            g.rng.below(u64::from(index)) as u32
        } else {
            index
        };
        let fields = g
            .fields(3)
            .into_iter()
            .enumerate()
            .map(|(i, ty)| FieldDef {
                name: format!("f{i}"),
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
            repr: StructRepr::C,
            origin: None,
        });
    }
    for index in 0..enums {
        let id = if index > 0 && g.rng.chance(8) {
            g.rng.below(u64::from(index)) as u32
        } else {
            index
        };
        let variants: Vec<EnumVariant> = (0..g.rng.below(3) + 1)
            .map(|v| EnumVariant {
                name: format!("V{v}"),
                fields: g.fields(2),
                field_names: Vec::new(),
            })
            .collect();
        let mut def = EnumDef::new(EnumId::new(id), format!("E{index}"), variants);
        def.layout = g.encoding(def.variants.len());
        module.enums.push(def);
    }
    let mut types: Vec<Ty> = (0..=structs)
        .map(|id| Ty::Struct(StructId::new(id)))
        .collect();
    types.extend((0..=enums).map(|id| Ty::Enum(EnumId::new(id))));
    types.extend((0..8).map(|_| g.ty(2)));
    (module, types)
}

#[test]
fn random_type_graphs_count_as_the_rules_say() {
    let mut census = Census::default();
    for case in 0..4000u64 {
        let (module, types) = random_module(case.wrapping_mul(0x9e37_79b9) ^ 0x1a7e5);
        compare(&format!("random {case}"), &module, &types, &mut census);
    }
    eprintln!("random graphs: {census:?}");
    assert!(census.admitted > 500, "{census:?}");
    assert!(census.refused > 500, "{census:?}");
}

// ---------------------------------------------------------------------------
// What the cut-off refused, and what it could not take
// ---------------------------------------------------------------------------

fn s(id: u32) -> Ty {
    Ty::Struct(StructId::new(id))
}

fn strukt(id: u32, fields: Vec<Ty>) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: format!("W{id}"),
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
        repr: StructRepr::C,
        origin: None,
    }
}

/// `W0 = { u64, *const u8 }`, `W{k} = { W{k-1} }`.
fn newtypes(depth: u32) -> Module {
    let mut module = Module::new("newtypes");
    module.target_info = Some(target());
    module
        .structs
        .push(strukt(0, vec![Ty::U64, Ty::PtrConst(Box::new(Ty::U8))]));
    for k in 1..=depth {
        module.structs.push(strukt(k, vec![s(k - 1)]));
    }
    module
}

#[test]
fn a_pair_under_any_number_of_newtypes_is_a_pair() {
    let module = newtypes(40);
    let types: Vec<Ty> = (0..=40).map(s).collect();
    let mut census = Census::default();
    compare("newtypes", &module, &types, &mut census);
    // Every level is a pair; the cut-off said so only for the top 16.
    assert_eq!(census.admitted, 41, "{census:?}");
    assert!(census.cut_off >= 24, "{census:?}");
    assert_eq!(capped(&module, &s(40), 0), None);

    // Far past where a recursion overflows: one validation pass over 10^5
    // newtypes, every 97th level claimed, on a small stack.
    let worker = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let depth = 100_000;
            let mut module = newtypes(depth);
            let types: Vec<Ty> = (0..=depth).step_by(97).map(s).collect();
            claim_pairs(&mut module, &types);
            assert_eq!(refused_pairs(&module), BTreeSet::new());
        })
        .expect("spawn");
    worker.join().expect("no stack overflow");
}

#[test]
fn a_by_value_cycle_has_no_count_from_any_entry_point() {
    // A ring through a struct and an enum, and a struct that reaches it.
    let mut module = Module::new("ring");
    module.target_info = Some(target());
    module
        .structs
        .push(strukt(0, vec![Ty::Enum(EnumId::new(0)), Ty::U64]));
    module.enums.push(EnumDef::new(
        EnumId::new(0),
        "E0",
        vec![EnumVariant {
            name: "V".into(),
            fields: vec![s(0)],
            field_names: Vec::new(),
        }],
    ));
    module.structs.push(strukt(1, vec![s(0)]));
    // A pair beside the ring, reached first: still a pair.
    module.structs.push(strukt(2, vec![Ty::U64, Ty::U64]));
    let types = vec![s(1), s(0), Ty::Enum(EnumId::new(0)), s(2), s(1), s(2)];
    let mut census = Census::default();
    compare("ring", &module, &types, &mut census);
    assert_eq!((census.admitted, census.refused), (2, 4), "{census:?}");
}

// ---------------------------------------------------------------------------
// Deep chains of every wrapper kind, against a second oracle
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Node {
    Struct(StructId),
    Enum(EnumId),
}

/// The struct and enum nodes a count of `ty` reads directly (through
/// tuples, the only inline aggregate the rules sum).
fn named(ty: &Ty, out: &mut Vec<Node>) {
    match ty {
        Ty::Tuple(fields) => fields.iter().for_each(|field| named(field, out)),
        Ty::Struct(id) => out.push(Node::Struct(*id)),
        Ty::Enum(id) => out.push(Node::Enum(*id)),
        _ => {}
    }
}

fn successors(module: &Module, node: Node) -> Vec<Node> {
    let mut out = Vec::new();
    match node {
        Node::Struct(id) => {
            if let Some(def) = module.structs.iter().find(|def| def.id == id) {
                def.fields
                    .iter()
                    .for_each(|field| named(&field.ty, &mut out));
            }
        }
        Node::Enum(id) => {
            if let Some(def) = module.enums.iter().find(|def| def.id == id) {
                if let Some(EnumTagEncoding::SingleInhabited { variant }) =
                    def.layout.as_ref().map(|layout| &layout.encoding)
                {
                    if let Some(selected) = selected_variant(module, def, *variant) {
                        def.variants[selected]
                            .fields
                            .iter()
                            .for_each(|ty| named(ty, &mut out));
                    }
                } else {
                    def.variants
                        .iter()
                        .flat_map(|variant| &variant.fields)
                        .for_each(|ty| named(ty, &mut out));
                }
            }
        }
    }
    out
}

/// The rules decided another way than [`uncapped`]: first, for each node,
/// whether it can reach a by-value cycle at all (its own DFS with on-stack
/// marks, no memo); a node that can has no count; every other node's count
/// is a recursion over an acyclic graph, memoized per node, so a doubling
/// tower costs its height and its overflow is reached. The two meet a cycle
/// differently: [`uncapped`] finds it on the path it walks, or never walks to
/// it because a rule short-circuits first (a `Niche` other variant with
/// lanes, a `Direct` payload of two, an `Untagged` enum of two variants);
/// here every node that can reach a cycle is "no count" outright. They agree
/// because every rule answers a count only after counting every member it
/// names, so each short-circuit is itself "no count".
struct WellFounded<'m> {
    module: &'m Module,
    cyclic: std::collections::HashMap<Node, bool>,
    counts: std::collections::HashMap<Node, Option<usize>>,
}

impl<'m> WellFounded<'m> {
    fn new(module: &'m Module) -> Self {
        WellFounded {
            module,
            cyclic: Default::default(),
            counts: Default::default(),
        }
    }

    fn reaches_a_cycle(&mut self, node: Node) -> bool {
        if let Some(&cyclic) = self.cyclic.get(&node) {
            return cyclic;
        }
        let mut on_path = std::collections::HashSet::new();
        let mut done = std::collections::HashSet::new();
        let mut stack = vec![(node, successors(self.module, node), 0usize)];
        on_path.insert(node);
        let mut cyclic = false;
        while let Some((at, next, index)) = stack.last_mut() {
            if let Some(&successor) = next.get(*index) {
                *index += 1;
                if on_path.contains(&successor) {
                    cyclic = true;
                    break;
                }
                if done.insert(successor) {
                    on_path.insert(successor);
                    let next = successors(self.module, successor);
                    stack.push((successor, next, 0));
                }
            } else {
                on_path.remove(at);
                stack.pop();
            }
        }
        self.cyclic.insert(node, cyclic);
        cyclic
    }

    fn sum<'a>(&mut self, fields: impl Iterator<Item = &'a Ty>) -> Option<usize> {
        let mut lanes = 0usize;
        for field in fields {
            lanes = lanes.checked_add(self.lanes(field)?)?;
        }
        Some(lanes)
    }

    fn lanes(&mut self, ty: &Ty) -> Option<usize> {
        let size_of = |ty: &Ty| {
            self.module
                .ty_layout_shape(ty)
                .ok()
                .and_then(|s| s.size_bytes())
        };
        let module = self.module;
        let node = match ty {
            _ if is_closed_scalar_ty(ty) => return Some(usize::from(size_of(ty)? != 0)),
            Ty::Ref(_) | Ty::RefMut(_) | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Rc(_) => {
                return Some(1);
            }
            Ty::FatPtr(_) => return Some(2),
            Ty::Tuple(fields) => return self.sum(fields.iter()),
            Ty::Struct(id) => Node::Struct(*id),
            Ty::Enum(id) => Node::Enum(*id),
            _ => return None,
        };
        if let Some(&count) = self.counts.get(&node) {
            return count;
        }
        let count = if self.reaches_a_cycle(node) {
            None
        } else {
            match node {
                Node::Struct(id) => match module.structs.iter().find(|def| def.id == id) {
                    Some(def) => self.sum(def.fields.iter().map(|f| &f.ty)),
                    None => None,
                },
                Node::Enum(id) => match module.enums.iter().find(|def| def.id == id) {
                    Some(def) => {
                        if def.variants.is_empty() {
                            return None;
                        }
                        if let Some(EnumTagEncoding::SingleInhabited { variant }) =
                            def.layout.as_ref().map(|layout| &layout.encoding)
                        {
                            return self.sum(
                                def.variants[selected_variant(module, def, *variant)?]
                                    .fields
                                    .iter(),
                            );
                        }
                        let variants: Vec<Option<usize>> = def
                            .variants
                            .iter()
                            .map(|variant| self.sum(variant.fields.iter()))
                            .collect();
                        match def.layout.as_ref().map(|layout| &layout.encoding) {
                            Some(EnumTagEncoding::SingleInhabited { .. }) => {
                                unreachable!("selected physical dependency handled above")
                            }
                            Some(EnumTagEncoding::Untagged) => match variants.as_slice() {
                                [only] => *only,
                                _ => None,
                            },
                            Some(EnumTagEncoding::Niche {
                                untagged_variant, ..
                            }) => {
                                let dataful = *untagged_variant as usize;
                                let others_empty = variants
                                    .iter()
                                    .enumerate()
                                    .all(|(index, lanes)| index == dataful || *lanes == Some(0));
                                if others_empty {
                                    variants.get(dataful).copied().flatten()
                                } else {
                                    None
                                }
                            }
                            Some(EnumTagEncoding::Direct { .. }) | None => {
                                if variants.iter().all(|lanes| matches!(lanes, Some(0 | 1))) {
                                    Some(1 + variants.iter().flatten().max().copied().unwrap_or(0))
                                } else {
                                    None
                                }
                            }
                        }
                    }
                    None => None,
                },
            }
        };
        self.counts.insert(node, count);
        count
    }
}

fn enum_def(id: u32, variants: Vec<Vec<Ty>>, encoding: EnumTagEncoding) -> EnumDef {
    let count = variants.len();
    let mut def = EnumDef::new(
        EnumId::new(id),
        format!("E{id}"),
        variants
            .into_iter()
            .enumerate()
            .map(|(v, fields)| EnumVariant {
                name: format!("V{v}"),
                fields,
                field_names: Vec::new(),
            })
            .collect(),
    );
    def.layout = Some(EnumLayoutDescriptor {
        encoding,
        size: 16,
        align: 8,
        variant_field_offsets: vec![Vec::new(); count],
    });
    def
}

fn niche(dataful: u32) -> EnumTagEncoding {
    EnumTagEncoding::Niche {
        untagged_variant: dataful,
        niche_variants_start: 0,
        niche_variants_end: 0,
        niche_start: 0,
        niche_offset: 0,
        niche_ty: EnumTagRepr::U8,
    }
}

/// What a deep chain stands on (struct 0).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Bottom {
    Pair,
    OneLane,
    ThreeLanes,
    /// A tagged enum with a one-lane payload: a tag lane and one more.
    TaggedOneLane,
    /// A tagged enum with a two-lane payload: a memory aggregate.
    TaggedTwoLanes,
    Missing,
    /// `{ u64, W(depth / 2) }`: the chain's lower half is a ring.
    RingToTheMiddle,
    /// `{ P70, u64, u64 }` with `P{k+1} = { Pk, Pk }`: 2^70 lanes, no count.
    Overflow,
}

const BOTTOMS: [Bottom; 8] = [
    Bottom::Pair,
    Bottom::OneLane,
    Bottom::ThreeLanes,
    Bottom::TaggedOneLane,
    Bottom::TaggedTwoLanes,
    Bottom::Missing,
    Bottom::RingToTheMiddle,
    Bottom::Overflow,
];

/// How one level wraps the level below it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Wrapper {
    Newtype,
    /// `{ ((), below), () }`.
    UnitTuple,
    /// A single-variant `Untagged` enum.
    Untagged,
    /// A `Niche` enum whose other variant is `()`.
    Niche,
}

const WRAPPERS: [Wrapper; 4] = [
    Wrapper::Newtype,
    Wrapper::UnitTuple,
    Wrapper::Untagged,
    Wrapper::Niche,
];

/// A chain of `wrappers` (level `k` wraps level `k - 1`) over `bottom`.
fn deep_chain(bottom: Bottom, wrappers: &[Wrapper]) -> Module {
    let depth = wrappers.len() as u32;
    let mut module = Module::new("deep");
    module.target_info = Some(target());
    let helpers = 1_000_000;
    match bottom {
        Bottom::Pair => module
            .structs
            .push(strukt(0, vec![Ty::U64, Ty::PtrConst(Box::new(Ty::U8))])),
        Bottom::OneLane => module.structs.push(strukt(0, vec![Ty::U64, Ty::Unit])),
        Bottom::ThreeLanes => module
            .structs
            .push(strukt(0, vec![Ty::U64, Ty::U32, Ty::U8])),
        Bottom::TaggedOneLane | Bottom::TaggedTwoLanes => {
            let payload = if bottom == Bottom::TaggedOneLane {
                vec![Ty::U64]
            } else {
                vec![Ty::U64, Ty::U64]
            };
            module
                .structs
                .push(strukt(0, vec![Ty::Enum(EnumId::new(helpers))]));
            module.enums.push(enum_def(
                helpers,
                vec![payload, Vec::new()],
                EnumTagEncoding::Direct { tag_offset: 0 },
            ));
        }
        Bottom::Missing => {}
        Bottom::RingToTheMiddle => module.structs.push(strukt(0, vec![Ty::U64, s(depth / 2)])),
        Bottom::Overflow => {
            module.structs.push(strukt(helpers, vec![Ty::U64]));
            for k in 1..=70 {
                module.structs.push(strukt(
                    helpers + k,
                    vec![s(helpers + k - 1), s(helpers + k - 1)],
                ));
            }
            module
                .structs
                .push(strukt(0, vec![s(helpers + 70), Ty::U64, Ty::U64]));
        }
    }
    for (k, wrapper) in (1..).zip(wrappers) {
        let below = s(k - 1);
        let wrapped = 2_000_000 + k;
        match wrapper {
            Wrapper::Newtype => module.structs.push(strukt(k, vec![below])),
            Wrapper::UnitTuple => module
                .structs
                .push(strukt(k, vec![Ty::Tuple(vec![Ty::Unit, below]), Ty::Unit])),
            Wrapper::Untagged => {
                module
                    .structs
                    .push(strukt(k, vec![Ty::Enum(EnumId::new(wrapped))]));
                module.enums.push(enum_def(
                    wrapped,
                    vec![vec![below]],
                    EnumTagEncoding::Untagged,
                ));
            }
            Wrapper::Niche => {
                module
                    .structs
                    .push(strukt(k, vec![Ty::Enum(EnumId::new(wrapped))]));
                module.enums.push(enum_def(
                    wrapped,
                    vec![vec![Ty::Unit], vec![below]],
                    niche(1),
                ));
            }
        }
    }
    module
}

#[test]
fn deep_chains_of_every_wrapper_count_as_the_rules_say() {
    let worker = std::thread::Builder::new()
        // The two oracles recurse once per level.
        .stack_size(256 * 1024 * 1024)
        .spawn(|| {
            let mut rng = Rng(0xdeeb_c4a1);
            // Per (bottom, wrapper kind present deeper than 16): the claims
            // above level 16 admitted and refused.
            let mut deep: std::collections::BTreeMap<(Bottom, Wrapper), (usize, usize)> =
                Default::default();
            let mut chains: Vec<(Bottom, Vec<Wrapper>)> = Vec::new();
            // Each wrapper alone over each bottom, then mixed chains.
            for bottom in BOTTOMS {
                for wrapper in WRAPPERS {
                    chains.push((bottom, vec![wrapper; 40]));
                }
            }
            for _ in 0..160 {
                let bottom = BOTTOMS[rng.below(BOTTOMS.len() as u64) as usize];
                let depth = 17 + rng.below(284) as usize;
                let wrappers = (0..depth)
                    .map(|_| WRAPPERS[rng.below(WRAPPERS.len() as u64) as usize])
                    .collect();
                chains.push((bottom, wrappers));
            }
            for (case, (bottom, wrappers)) in chains.iter().enumerate() {
                let depth = wrappers.len() as u32;
                let mut module = deep_chain(*bottom, wrappers);
                // Some levels first (so a claim deep in the chain decides the
                // levels below it before the bottom is asked), the top, then
                // every level: one validation pass, one memo.
                let mut levels: Vec<u32> = (0..6)
                    .map(|_| rng.below(u64::from(depth) + 1) as u32)
                    .collect();
                levels.push(depth);
                levels.extend(0..=depth);
                let types: Vec<Ty> = levels.iter().map(|&k| s(k)).collect();
                let ids = claim_pairs(&mut module, &types);
                let refused = refused_pairs(&module);
                let mut oracle = WellFounded::new(&module);
                for ((&level, ty), id) in levels.iter().zip(&types).zip(ids) {
                    let want = oracle.lanes(ty);
                    let label = format!("chain {case} ({bottom:?}, depth {depth}) level {level}");
                    assert_eq!(refused.contains(&id), want != Some(2), "{label}: {want:?}");
                    // The path-guard recursion walks a tower per path: asked
                    // everywhere else, at a few levels.
                    if *bottom != Bottom::Overflow && (level == depth || level % 37 == 0) {
                        assert_eq!(uncapped(&module, ty, &mut Vec::new()), want, "{label}");
                    }
                    if level > 16 {
                        let mut kinds: Vec<Wrapper> = wrappers[..level as usize].to_vec();
                        kinds.sort();
                        kinds.dedup();
                        for kind in kinds {
                            let entry = deep.entry((*bottom, kind)).or_default();
                            if want == Some(2) {
                                entry.0 += 1;
                            } else {
                                entry.1 += 1;
                            }
                        }
                    }
                }
            }
            eprintln!("deep chains: {deep:?}");
            // Every wrapper kind carries an admitted pair deeper than the
            // old cut-off over each bottom that is a pair, and a refusal over
            // every other bottom.
            for bottom in BOTTOMS {
                for wrapper in WRAPPERS {
                    let (admitted, refused) =
                        deep.get(&(bottom, wrapper)).copied().unwrap_or_default();
                    if matches!(bottom, Bottom::Pair | Bottom::TaggedOneLane) {
                        assert!(
                            admitted > 20 && refused == 0,
                            "{bottom:?} {wrapper:?}: {deep:?}"
                        );
                    } else {
                        assert!(
                            admitted == 0 && refused > 20,
                            "{bottom:?} {wrapper:?}: {deep:?}"
                        );
                    }
                }
            }
        })
        .expect("spawn");
    worker.join().expect("the chains count as the rules say");
}
