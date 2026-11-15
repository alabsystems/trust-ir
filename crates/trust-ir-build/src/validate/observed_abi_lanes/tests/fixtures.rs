// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn module() -> Module {
    let mut module = Module::new("abi_lanes");
    module.target_info = Some(TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    module
}

pub(super) fn s(id: u32) -> Ty {
    Ty::Struct(StructId::new(id))
}

pub(super) fn strukt(id: u32, fields: Vec<Ty>) -> StructDef {
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
        repr: StructRepr::C,
        origin: None,
    }
}

/// `P0 = { u64 }`, `P{k+1} = { Pk, Pk }`: `2^k` lanes, a count that stops
/// fitting `usize` at 64 levels.
pub(super) fn doubling(depth: u32) -> Module {
    let mut module = module();
    module.structs.push(strukt(0, vec![Ty::U64]));
    for k in 1..=depth {
        module.structs.push(strukt(k, vec![s(k - 1), s(k - 1)]));
    }
    module
}

/// splitmix64.
struct Rng(u64);

impl Rng {
    fn below(&mut self, n: u64) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        (z ^ (z >> 31)) % n.max(1)
    }
}

pub(super) fn enum_def(
    id: u32,
    variants: Vec<Vec<Ty>>,
    encoding: Option<EnumTagEncoding>,
) -> EnumDef {
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
    def.layout = encoding.map(|encoding| trust_ir::ty::EnumLayoutDescriptor {
        encoding,
        size: 16,
        align: 8,
        variant_field_offsets: vec![Vec::new(); count],
    });
    def
}

pub(super) fn niche(dataful: u32) -> EnumTagEncoding {
    EnumTagEncoding::Niche {
        untagged_variant: dataful,
        niche_variants_start: 0,
        niche_variants_end: 0,
        niche_start: 0,
        niche_offset: 0,
        niche_ty: trust_ir::ty::EnumTagRepr::U8,
    }
}

/// A field of a random graph over `nodes` structs and enums (ids one past
/// the end are missing): payloads of zero, one, two and three lanes are
/// all common, so every arm of the enum rule meets every width.
fn random_field(rng: &mut Rng, nodes: u32, depth: u32) -> Ty {
    match rng.below(20) {
        0 => Ty::U64,
        1 => Ty::Bool,
        2 => Ty::Unit,
        3 => Ty::Ptr,
        4 => Ty::Ref(Box::new(Ty::U8)),
        5 => Ty::FatPtr(trust_ir::ty::FatPtrKind::Str),
        6 => Ty::Array(trust_ir::value::TyId::new(0), 1),
        7 => Ty::Tuple(vec![Ty::U64, Ty::U32]),
        8 => Ty::Tuple(Vec::new()),
        9..=12 => s(rng.below(u64::from(nodes) + 1) as u32),
        13..=16 => Ty::Enum(EnumId::new(rng.below(u64::from(nodes) + 1) as u32)),
        _ if depth > 0 => Ty::Tuple(
            (0..rng.below(3))
                .map(|_| random_field(rng, nodes, depth - 1))
                .collect(),
        ),
        _ => Ty::U32,
    }
}

pub(super) fn random_graph(seed: u64) -> Module {
    let mut rng = Rng(seed);
    let nodes = 1 + rng.below(10) as u32;
    let mut module = module();
    for index in 0..nodes {
        // A duplicate id now and then: the first definition counts.
        let id = if index > 0 && rng.below(10) == 0 {
            rng.below(u64::from(index)) as u32
        } else {
            index
        };
        let fields = (0..rng.below(4))
            .map(|_| random_field(&mut rng, nodes, 1))
            .collect();
        module.structs.push(strukt(id, fields));
        let variants: Vec<Vec<Ty>> = (0..1 + rng.below(3))
            .map(|_| {
                (0..rng.below(3))
                    .map(|_| random_field(&mut rng, nodes, 1))
                    .collect()
            })
            .collect();
        let encoding = match rng.below(5) {
            0 => None,
            1 | 2 => Some(EnumTagEncoding::Direct { tag_offset: 0 }),
            3 => Some(EnumTagEncoding::Untagged),
            // Now and then a dataful index past the variants.
            _ => Some(niche(rng.below(variants.len() as u64 + 1) as u32)),
        };
        module.enums.push(enum_def(id, variants, encoding));
    }
    module
}
