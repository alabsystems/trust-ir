// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The ABI lane count of a slot type, for the placement of a `pair` claim
//! (roadmap WS3.11): see [`abi_lanes`].

use std::cell::{Cell, RefCell};
use std::collections::HashMap;

use trust_ir::LayoutTable;
use trust_ir::ty::{EnumDef, EnumTagEncoding, Ty};
use trust_ir::value::{EnumId, StructId};

use super::is_closed_scalar_ty;

/// The number of ABI LANES a value of `ty` occupies when it is passed in
/// registers — rustc's `Scalar` (1) / `ScalarPair` (2) verdict counted
/// structurally — or `None` when the type is passed as a memory aggregate,
/// has no computable layout, or is not a register-class type at all.
///
/// * a closed scalar or a thin reference / raw pointer / `Rc` is one lane,
///   except that a zero-sized one (`()`) is none;
/// * a fat pointer is two lanes;
/// * a tuple or struct is the SUM of its fields' lanes, with `None` if any
///   field has none (arrays are never register-class, so `[u32; 1]` is
///   `None` even though it is one word — rustc agrees);
/// * an enum is counted under its tag encoding: `Untagged` is its sole
///   variant; `Niche` is the dataful (untagged) variant when every other
///   variant has no lanes (rustc's `others_zst`), else `None`; `Direct`, or
///   no descriptor (the canonical tagged union), is one tag lane plus the
///   widest payload, admitted only when every variant's payload is at most
///   one lane (a two-lane payload beside a tag is a memory aggregate);
/// * everything else (`Array`, `Vector`, `Record`, `Closure`, `Handle`,
///   `Dialect`, …) is `None`.
///
/// This decides PLACEMENT of a producer's `Pair` claim, not its truth: the
/// target classifier's own verdict stays trust-cg's cross-check (WS7).
///
/// A struct or enum reached again while its own count is open is a by-value
/// cycle, which has no finite lane count: `None`, for it and for everything
/// on the path that reached it. A count that does not fit `usize` is `None`
/// too (no register class has that many lanes). There is no depth bound: the
/// walk was a recursion cut off at 16 levels, which refused a `pair` on a
/// two-lane value wrapped in 17 newtypes (rustc stamps `ScalarPair` at any
/// depth), walked a shared sub-type once per path (`2^16` paths at the
/// bound) and scanned the struct or enum list at every level. It is now an
/// explicit-stack walk whose counts [`AbiLanes`] keeps per struct and enum
/// for the whole pass, so every `pair` claim of a module costs O(the type
/// graph it reaches) together.
pub(super) fn abi_lanes(layouts: &LayoutTable<'_>, memo: &AbiLanes, ty: &Ty) -> Option<usize> {
    memo.lanes(layouts, ty)
}

/// The [`abi_lanes`] count of each struct and enum, decided once per pass:
/// `Open` while its fields are being counted (a re-entry is a by-value
/// cycle), then the count.
#[derive(Default)]
pub(super) struct AbiLanes {
    nodes: RefCell<HashMap<AbiLaneNode, AbiLaneSlot>>,
    /// Types entered and counts handed on: O(the type graph the pass's
    /// `pair` claims reach), whatever the number of claims.
    steps: Cell<u64>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum AbiLaneNode {
    Struct(StructId),
    Enum(EnumId),
}

#[derive(Debug, Clone, Copy)]
enum AbiLaneSlot {
    Open,
    Counted(Option<usize>),
}

/// How an enum's count combines its variants' counts (the arms of
/// [`abi_lanes`]'s enum rule), in the order the rule reads them.
#[derive(Debug, Clone, Copy)]
enum AbiLaneEnumRule {
    /// The sole variant's lanes.
    Untagged,
    /// Every variant but the dataful one (counted last) has no lanes; then
    /// the dataful variant's lanes.
    Niche,
    /// Every variant has at most one lane: a tag lane plus the widest.
    Direct { widest: usize },
}

/// A frame of [`AbiLanes::lanes`]' explicit stack: a list of types whose
/// lanes are summed, owned by a struct, by one variant of the enum frame
/// below it, or by an inline tuple.
enum AbiLaneFrame<'m> {
    Sum {
        fields: Vec<&'m Ty>,
        next: usize,
        lanes: usize,
        owner: AbiLaneOwner,
    },
    Enum {
        id: EnumId,
        def: &'m EnumDef,
        rule: AbiLaneEnumRule,
        /// The variants in the order the rule reads them, and how many are
        /// counted.
        order: Vec<usize>,
        counted: usize,
    },
}

#[derive(Debug, Clone, Copy)]
enum AbiLaneOwner {
    Inline,
    Struct(StructId),
    Variant,
}

impl AbiLanes {
    fn lanes(&self, layouts: &LayoutTable<'_>, root: &Ty) -> Option<usize> {
        let mut stack: Vec<AbiLaneFrame<'_>> = Vec::new();
        // `Ok(ty)`: count `ty`; `Err(count)`: hand `count` to the frame on top.
        let mut step: Result<&Ty, Option<usize>> = Ok(root);
        loop {
            self.steps.set(self.steps.get() + 1);
            step = match step {
                Ok(ty) => self.enter(layouts, &mut stack, ty),
                Err(count) => match stack.last_mut() {
                    None => return count,
                    Some(_) => self.resume(&mut stack, count),
                },
            };
        }
    }

    fn record(&self, node: AbiLaneNode, count: Option<usize>) {
        self.nodes
            .borrow_mut()
            .insert(node, AbiLaneSlot::Counted(count));
    }

    /// Start counting `ty`: a count at once, or a frame and its first type.
    fn enter<'m>(
        &self,
        layouts: &LayoutTable<'m>,
        stack: &mut Vec<AbiLaneFrame<'m>>,
        ty: &'m Ty,
    ) -> Result<&'m Ty, Option<usize>> {
        let size_of = |ty: &Ty| layouts.ty_layout(ty).ok().and_then(|s| s.size_bytes());
        match ty {
            _ if is_closed_scalar_ty(ty) => Err(size_of(ty).map(|size| usize::from(size != 0))),
            Ty::Ref(_) | Ty::RefMut(_) | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Rc(_) => {
                Err(Some(1))
            }
            Ty::FatPtr(_) => Err(Some(2)),
            Ty::Tuple(fields) => self.sum(stack, fields.iter().collect(), AbiLaneOwner::Inline),
            Ty::Struct(id) => {
                let node = AbiLaneNode::Struct(*id);
                if let Some(slot) = self.nodes.borrow().get(&node) {
                    return Err(match slot {
                        AbiLaneSlot::Counted(count) => *count,
                        // A by-value cycle.
                        AbiLaneSlot::Open => None,
                    });
                }
                let Some(def) = layouts.struct_def(*id) else {
                    self.record(node, None);
                    return Err(None);
                };
                self.nodes.borrow_mut().insert(node, AbiLaneSlot::Open);
                self.sum(
                    stack,
                    def.fields.iter().map(|f| &f.ty).collect(),
                    AbiLaneOwner::Struct(*id),
                )
            }
            Ty::Enum(id) => {
                let node = AbiLaneNode::Enum(*id);
                if let Some(slot) = self.nodes.borrow().get(&node) {
                    return Err(match slot {
                        AbiLaneSlot::Counted(count) => *count,
                        AbiLaneSlot::Open => None,
                    });
                }
                let Some(def) = layouts.enum_def(*id) else {
                    self.record(node, None);
                    return Err(None);
                };
                let variants = def.variants.len();
                if variants == 0 {
                    self.record(node, None);
                    return Err(None);
                }
                let (rule, order): (AbiLaneEnumRule, Vec<usize>) =
                    match def.layout.as_ref().map(|layout| &layout.encoding) {
                        Some(EnumTagEncoding::Untagged) => {
                            if variants != 1 {
                                self.record(node, None);
                                return Err(None);
                            }
                            (AbiLaneEnumRule::Untagged, vec![0])
                        }
                        Some(EnumTagEncoding::SingleInhabited { variant }) => {
                            let active = *variant as usize;
                            if active >= variants
                                || layouts.variant_is_uninhabited(&def.variants[active])
                                || def.variants.iter().enumerate().any(|(index, item)| {
                                    index != active && !layouts.variant_is_uninhabited(item)
                                })
                            {
                                self.record(node, None);
                                return Err(None);
                            }
                            (AbiLaneEnumRule::Untagged, vec![active])
                        }
                        Some(EnumTagEncoding::Niche {
                            untagged_variant, ..
                        }) => {
                            let dataful = *untagged_variant as usize;
                            let mut order: Vec<usize> =
                                (0..variants).filter(|&index| index != dataful).collect();
                            // A dataful index past the variants has no lanes
                            // to count: the rule answers `None` once the
                            // others are counted.
                            order.push(dataful);
                            (AbiLaneEnumRule::Niche, order)
                        }
                        Some(EnumTagEncoding::Direct { .. }) | None => (
                            AbiLaneEnumRule::Direct { widest: 0 },
                            (0..variants).collect(),
                        ),
                    };
                self.nodes.borrow_mut().insert(node, AbiLaneSlot::Open);
                stack.push(AbiLaneFrame::Enum {
                    id: *id,
                    def,
                    rule,
                    order,
                    counted: 0,
                });
                self.next_variant(stack)
            }
            _ => Err(None),
        }
    }

    /// Push a sum over `fields`, or answer an empty one.
    fn sum<'m>(
        &self,
        stack: &mut Vec<AbiLaneFrame<'m>>,
        fields: Vec<&'m Ty>,
        owner: AbiLaneOwner,
    ) -> Result<&'m Ty, Option<usize>> {
        let Some(&first) = fields.first() else {
            return self.summed(stack, owner, Some(0));
        };
        stack.push(AbiLaneFrame::Sum {
            fields,
            next: 1,
            lanes: 0,
            owner,
        });
        Ok(first)
    }

    /// The enum frame on top counts its next variant, or finishes.
    fn next_variant<'m>(&self, stack: &mut Vec<AbiLaneFrame<'m>>) -> Result<&'m Ty, Option<usize>> {
        let Some(AbiLaneFrame::Enum {
            id,
            def,
            rule,
            order,
            counted,
        }) = stack.last()
        else {
            unreachable!("next_variant is asked of an enum frame");
        };
        let (id, def, rule) = (*id, *def, *rule);
        if let Some(&index) = order.get(*counted) {
            let Some(variant) = def.variants.get(index) else {
                // The niche rule's dataful index names no variant.
                stack.pop();
                self.record(AbiLaneNode::Enum(id), None);
                return Err(None);
            };
            return self.sum(
                stack,
                variant.fields.iter().collect(),
                AbiLaneOwner::Variant,
            );
        }
        stack.pop();
        let count = match rule {
            // Each answered when its last variant was counted (`resume`).
            AbiLaneEnumRule::Untagged | AbiLaneEnumRule::Niche => None,
            AbiLaneEnumRule::Direct { widest } => Some(1 + widest),
        };
        self.record(AbiLaneNode::Enum(id), count);
        Err(count)
    }

    /// Hand `count` to the frame on top.
    fn resume<'m>(
        &self,
        stack: &mut Vec<AbiLaneFrame<'m>>,
        count: Option<usize>,
    ) -> Result<&'m Ty, Option<usize>> {
        match stack.last_mut() {
            Some(AbiLaneFrame::Sum {
                fields,
                next,
                lanes,
                owner,
            }) => {
                let owner = *owner;
                let total = count.and_then(|count| lanes.checked_add(count));
                match (total, fields.get(*next).copied()) {
                    (Some(total), Some(field)) => {
                        *lanes = total;
                        *next += 1;
                        Ok(field)
                    }
                    (total, _) => {
                        stack.pop();
                        self.summed(stack, owner, total)
                    }
                }
            }
            Some(AbiLaneFrame::Enum { .. }) => {
                unreachable!("an enum frame is handed counts through its variants' sums")
            }
            None => Err(count),
        }
    }

    /// A sum (its frame popped, if it had one) came to `total`: hand it to
    /// its owner.
    fn summed<'m>(
        &self,
        stack: &mut Vec<AbiLaneFrame<'m>>,
        owner: AbiLaneOwner,
        total: Option<usize>,
    ) -> Result<&'m Ty, Option<usize>> {
        match owner {
            AbiLaneOwner::Inline => Err(total),
            AbiLaneOwner::Struct(id) => {
                self.record(AbiLaneNode::Struct(id), total);
                Err(total)
            }
            AbiLaneOwner::Variant => self.variant_counted(stack, total),
        }
    }

    /// The enum frame on top has counted one more variant: `lanes`.
    fn variant_counted<'m>(
        &self,
        stack: &mut Vec<AbiLaneFrame<'m>>,
        lanes: Option<usize>,
    ) -> Result<&'m Ty, Option<usize>> {
        let Some(AbiLaneFrame::Enum {
            id,
            rule,
            order,
            counted,
            ..
        }) = stack.last_mut()
        else {
            unreachable!("a variant's sum sits on its enum's frame");
        };
        let id = *id;
        *counted += 1;
        let last = *counted == order.len();
        // `Some(count)`: the enum's count is decided; `None`: count the next
        // variant.
        let decided: Option<Option<usize>> = match (rule, lanes) {
            (_, None) => Some(None),
            (AbiLaneEnumRule::Untagged, lanes) => Some(lanes),
            (AbiLaneEnumRule::Niche, lanes) if last => Some(lanes),
            (AbiLaneEnumRule::Niche, Some(0)) => None,
            (AbiLaneEnumRule::Niche, Some(_)) => Some(None),
            (AbiLaneEnumRule::Direct { .. }, Some(lanes)) if lanes > 1 => Some(None),
            (AbiLaneEnumRule::Direct { widest }, Some(lanes)) => {
                *widest = (*widest).max(lanes);
                None
            }
        };
        match decided {
            Some(count) => {
                stack.pop();
                self.record(AbiLaneNode::Enum(id), count);
                Err(count)
            }
            None => self.next_variant(stack),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::ty::{EnumVariant, FieldDef, StructDef, StructRepr};
    use trust_ir::{Endianness, Module, TargetInfo};

    fn module() -> Module {
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

    fn s(id: u32) -> Ty {
        Ty::Struct(StructId::new(id))
    }

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
            repr: StructRepr::C,
            origin: None,
        }
    }

    /// `P0 = { u64 }`, `P{k+1} = { Pk, Pk }`: `2^k` lanes, a count that stops
    /// fitting `usize` at 64 levels.
    fn doubling(depth: u32) -> Module {
        let mut module = module();
        module.structs.push(strukt(0, vec![Ty::U64]));
        for k in 1..=depth {
            module.structs.push(strukt(k, vec![s(k - 1), s(k - 1)]));
        }
        module
    }

    #[test]
    fn shared_sub_types_are_counted_once_and_overflow_is_no_count() {
        // The work bound FIRST, where a walk per path (2^20) still ends.
        let small = doubling(20);
        let table = small.layout_table();
        let lanes = AbiLanes::default();
        assert_eq!(abi_lanes(&table, &lanes, &s(20)), Some(1 << 20));
        assert!(lanes.steps.get() <= 3 * 41 + 4, "{}", lanes.steps.get());
        assert_eq!(abi_lanes(&table, &lanes, &s(1)), Some(2));

        let deep = doubling(100_000);
        let table = deep.layout_table();
        let lanes = AbiLanes::default();
        assert_eq!(abi_lanes(&table, &lanes, &s(63)), Some(1 << 63));
        // 2^64 lanes do not fit: no register class has them.
        assert_eq!(abi_lanes(&table, &lanes, &s(64)), None);
        assert_eq!(abi_lanes(&table, &lanes, &s(100_000)), None);
        assert!(
            lanes.steps.get() <= 3 * 200_001 + 8,
            "{}",
            lanes.steps.get()
        );
        // Every other count is a lookup.
        let before = lanes.steps.get();
        for k in (0..100_000).step_by(997) {
            abi_lanes(&table, &lanes, &s(k));
        }
        assert!(
            lanes.steps.get() - before <= 2 * 101,
            "{}",
            lanes.steps.get()
        );
    }

    #[test]
    fn deep_chains_and_cycles_are_counted_on_a_small_stack() {
        let worker = std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                // A two-lane pair under 10^5 newtypes, and an enum chain
                // (each `Direct` level a tag lane plus a one-lane payload
                // only at the bottom).
                let depth = 100_000u32;
                let mut chain = module();
                chain.structs.push(strukt(0, vec![Ty::U64, Ty::Ptr]));
                chain.enums.push(trust_ir::ty::EnumDef::new(
                    EnumId::new(0),
                    "E0",
                    vec![EnumVariant {
                        name: "V".into(),
                        fields: vec![Ty::U32],
                        field_names: Vec::new(),
                    }],
                ));
                for k in 1..depth {
                    chain.structs.push(strukt(k, vec![s(k - 1)]));
                    chain.enums.push(trust_ir::ty::EnumDef::new(
                        EnumId::new(k),
                        format!("E{k}"),
                        vec![EnumVariant {
                            name: "V".into(),
                            fields: vec![Ty::Enum(EnumId::new(k - 1))],
                            field_names: Vec::new(),
                        }],
                    ));
                }
                let table = chain.layout_table();
                let lanes = AbiLanes::default();
                assert_eq!(abi_lanes(&table, &lanes, &s(depth - 1)), Some(2));
                // E1 = tag + E0 (2 lanes): a two-lane payload beside a tag
                // is a memory aggregate.
                assert_eq!(
                    abi_lanes(&table, &lanes, &Ty::Enum(EnumId::new(0))),
                    Some(2)
                );
                assert_eq!(abi_lanes(&table, &lanes, &Ty::Enum(EnumId::new(1))), None);
                assert_eq!(
                    abi_lanes(&table, &lanes, &Ty::Enum(EnumId::new(depth - 1))),
                    None
                );
                assert!(
                    lanes.steps.get() <= 8 * u64::from(depth),
                    "{}",
                    lanes.steps.get()
                );

                // The same chain closed into a ring at the bottom: no count,
                // from every entry point.
                let mut ring = chain.clone();
                ring.structs[0] = strukt(0, vec![s(depth - 1), Ty::U64]);
                let table = ring.layout_table();
                let lanes = AbiLanes::default();
                for k in [depth - 1, 0, depth / 2] {
                    assert_eq!(abi_lanes(&table, &lanes, &s(k)), None, "{k}");
                }
                assert!(
                    lanes.steps.get() <= 8 * u64::from(depth),
                    "{}",
                    lanes.steps.get()
                );
            })
            .expect("spawn");
        worker.join().expect("no stack overflow");
    }
    // -----------------------------------------------------------------------
    // Exact counts against the rules as a plain recursion
    // -----------------------------------------------------------------------

    /// The rules of [`abi_lanes`] as a plain recursion: no memo, no depth
    /// cut-off, a struct or enum re-entered on its own path is a cycle (no
    /// count), a sum that does not fit is no count, an id resolves to its
    /// first definition. It answers the EXACT count, so a wrong count that is
    /// not two (which the validator's `pair` verdict cannot see) differs too.
    fn rule(module: &Module, ty: &Ty, path: &mut Vec<AbiLaneNode>) -> Option<usize> {
        fn sum<'a>(
            module: &Module,
            fields: impl Iterator<Item = &'a Ty>,
            path: &mut Vec<AbiLaneNode>,
        ) -> Option<usize> {
            let mut lanes = 0usize;
            for field in fields {
                lanes = lanes.checked_add(rule(module, field, path)?)?;
            }
            Some(lanes)
        }
        let size_of = |ty: &Ty| module.ty_layout_shape(ty).ok().and_then(|s| s.size_bytes());
        match ty {
            _ if is_closed_scalar_ty(ty) => Some(usize::from(size_of(ty)? != 0)),
            Ty::Ref(_) | Ty::RefMut(_) | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Rc(_) => Some(1),
            Ty::FatPtr(_) => Some(2),
            Ty::Tuple(fields) => sum(module, fields.iter(), path),
            Ty::Struct(id) => {
                let def = module.structs.iter().find(|def| def.id == *id)?;
                let node = AbiLaneNode::Struct(*id);
                if path.contains(&node) {
                    return None;
                }
                path.push(node);
                let lanes = sum(module, def.fields.iter().map(|f| &f.ty), path);
                path.pop();
                lanes
            }
            Ty::Enum(id) => {
                let def = module.enums.iter().find(|def| def.id == *id)?;
                if def.variants.is_empty() {
                    return None;
                }
                let node = AbiLaneNode::Enum(*id);
                if path.contains(&node) {
                    return None;
                }
                path.push(node);
                let variant = |index: usize, path: &mut Vec<AbiLaneNode>| -> Option<usize> {
                    sum(module, def.variants.get(index)?.fields.iter(), path)
                };
                let lanes = (|| match def.layout.as_ref().map(|layout| &layout.encoding) {
                    Some(EnumTagEncoding::SingleInhabited { variant: selected }) => {
                        let selected = *selected as usize;
                        let mut inhabitedness = trust_ir::Inhabitedness::for_module(module);
                        if selected >= def.variants.len()
                            || def.variants.iter().enumerate().any(|(index, item)| {
                                inhabitedness.variant_is_uninhabited(item) == (index == selected)
                            })
                        {
                            return None;
                        }
                        variant(selected, path)
                    }
                    Some(EnumTagEncoding::Untagged) => (def.variants.len() == 1)
                        .then(|| variant(0, path))
                        .flatten(),
                    Some(EnumTagEncoding::Niche {
                        untagged_variant, ..
                    }) => {
                        let dataful = *untagged_variant as usize;
                        for index in 0..def.variants.len() {
                            if index != dataful && variant(index, path)? != 0 {
                                return None;
                            }
                        }
                        variant(dataful, path)
                    }
                    Some(EnumTagEncoding::Direct { .. }) | None => {
                        let mut widest = 0usize;
                        for index in 0..def.variants.len() {
                            let lanes = variant(index, path)?;
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

    fn enum_def(id: u32, variants: Vec<Vec<Ty>>, encoding: Option<EnumTagEncoding>) -> EnumDef {
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

    fn niche(dataful: u32) -> EnumTagEncoding {
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

    fn random_graph(seed: u64) -> Module {
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

    #[test]
    fn random_graphs_count_exactly_as_the_rules_say() {
        // Per answer (`None` as `usize::MAX`): how often it was seen.
        let mut seen: std::collections::BTreeMap<usize, usize> = Default::default();
        let mut two_lane_payloads = 0usize;
        for case in 0..3000u64 {
            let module = random_graph(case.wrapping_mul(0x9e37_79b9) ^ 0xab1_1a7e);
            let table = module.layout_table();
            let lanes = AbiLanes::default();
            let nodes = module.structs.len() as u32;
            let mut types: Vec<Ty> = (0..=nodes).map(s).collect();
            types.extend((0..=nodes).map(|id| Ty::Enum(EnumId::new(id))));
            // Shuffled, then each asked again: a memo verdict must not
            // depend on which claim reached it first.
            let mut order: Vec<usize> = (0..types.len()).collect();
            for i in (1..order.len()).rev() {
                order.swap(i, Rng(case ^ i as u64).below(i as u64 + 1) as usize);
            }
            for &index in order.iter().chain(&order) {
                let ty = &types[index];
                let want = rule(&module, ty, &mut Vec::new());
                assert_eq!(abi_lanes(&table, &lanes, ty), want, "case {case}: {ty:?}");
                *seen.entry(want.unwrap_or(usize::MAX)).or_default() += 1;
                // A tagged enum one of whose payloads is two lanes: a memory
                // aggregate, whatever it would add up to.
                if let Ty::Enum(id) = ty
                    && let Some(def) = module.enums.iter().find(|def| def.id == *id)
                    && matches!(
                        def.layout.as_ref().map(|layout| &layout.encoding),
                        None | Some(EnumTagEncoding::Direct { .. })
                    )
                    && def.variants.iter().any(|variant| {
                        let payload = Ty::Tuple(variant.fields.clone());
                        rule(&module, &payload, &mut vec![AbiLaneNode::Enum(*id)]) == Some(2)
                    })
                {
                    assert_eq!(want, None, "case {case}: {ty:?}");
                    two_lane_payloads += 1;
                }
            }
        }
        // Not vacuous: every count up to three, wider ones, no count, and
        // tagged enums with a two-lane payload are all met.
        for count in [0, 1, 2, 3, usize::MAX] {
            assert!(
                seen.get(&count).copied().unwrap_or(0) > 200,
                "{count}: {seen:?}"
            );
        }
        assert!(
            seen.range(4..usize::MAX).map(|(_, n)| n).sum::<usize>() > 200,
            "{seen:?}"
        );
        assert!(two_lane_payloads > 200, "{two_lane_payloads}");
    }

    /// Each wrapper over each bottom, exact counts, deeper than any cut-off.
    #[test]
    fn deep_wrappers_count_exactly_as_the_rules_say() {
        // Bottoms (struct 0): a pair; one lane; three lanes; a tagged enum
        // with a one-lane payload (two lanes) and with a two-lane payload
        // (none); a missing definition; a ring to the chain's middle.
        let depth = 40u32;
        for bottom in 0..7 {
            for wrapper in 0..4 {
                let mut module = module();
                let tagged = 1_000_000;
                match bottom {
                    0 => module.structs.push(strukt(0, vec![Ty::U64, Ty::Ptr])),
                    1 => module.structs.push(strukt(0, vec![Ty::U64, Ty::Unit])),
                    2 => module
                        .structs
                        .push(strukt(0, vec![Ty::U64, Ty::U32, Ty::U8])),
                    3 | 4 => {
                        let payload = if bottom == 3 {
                            vec![Ty::U64]
                        } else {
                            vec![Ty::U64, Ty::U64]
                        };
                        module
                            .structs
                            .push(strukt(0, vec![Ty::Enum(EnumId::new(tagged))]));
                        module.enums.push(enum_def(
                            tagged,
                            vec![payload, Vec::new()],
                            Some(EnumTagEncoding::Direct { tag_offset: 0 }),
                        ));
                    }
                    5 => {}
                    _ => module.structs.push(strukt(0, vec![Ty::U64, s(depth / 2)])),
                }
                for k in 1..=depth {
                    let below = s(k - 1);
                    let wrapped = 2_000_000 + k;
                    match wrapper {
                        0 => module.structs.push(strukt(k, vec![below])),
                        1 => module
                            .structs
                            .push(strukt(k, vec![Ty::Tuple(vec![Ty::Unit, below]), Ty::Unit])),
                        2 => {
                            module
                                .structs
                                .push(strukt(k, vec![Ty::Enum(EnumId::new(wrapped))]));
                            module.enums.push(enum_def(
                                wrapped,
                                vec![vec![below]],
                                Some(EnumTagEncoding::Untagged),
                            ));
                        }
                        _ => {
                            module
                                .structs
                                .push(strukt(k, vec![Ty::Enum(EnumId::new(wrapped))]));
                            module.enums.push(enum_def(
                                wrapped,
                                vec![vec![Ty::Unit], vec![below]],
                                Some(niche(1)),
                            ));
                        }
                    }
                }
                let want = [Some(2), Some(1), Some(3), Some(2), None, None, None][bottom];
                let table = module.layout_table();
                let lanes = AbiLanes::default();
                for k in [depth, depth / 2 + 1, 0, depth / 2, depth - 1] {
                    let got = abi_lanes(&table, &lanes, &s(k));
                    assert_eq!(
                        got,
                        rule(&module, &s(k), &mut Vec::new()),
                        "{bottom} {wrapper} {k}"
                    );
                    assert_eq!(got, want, "bottom {bottom}, wrapper {wrapper}, level {k}");
                }
            }
        }
    }
}
