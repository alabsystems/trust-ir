//! The layout recursion `LayoutTable` replaced, verbatim (trust-ir
//! 8d3895d8, `crates/trust-ir/src/shape.rs` and the two `EnumDef` helpers of
//! `ty.rs` it called), as free functions over a `Module`. Only `self.` became
//! `m.`, and a call of a crate helper became a call of its copy here, so the
//! oracle shares no code the table's change touched: `effective_discriminants`
//! and `canonical_tag_repr` (now a hash set in the crate), and
//! `tuple_layout_descriptor`. Do not "fix" it: it is the definition the table
//! must reproduce.
//!
//! The one deliberate change of meaning is inhabitedness, which the niche
//! rule asks. The crate now decides it as the LEAST solution of its rules
//! (`trust_ir::Module::ty_is_uninhabited`); the oracle's niche rule asks
//! [`least_fixpoint`], a naive iterate-until-stable statement of exactly
//! that, and keeps the recursion it replaced verbatim beside it
//! ([`old_ty_is_uninhabited`], [`old_variant_is_uninhabited`]) so the
//! differential can show where, and only where, the two differ.
//!
//! One extension of the recursion, not a change of it: the declared closure
//! layouts of wire v58 (WS3.9 / WS3.13). The recursion they were written for
//! threaded a `closure_visiting` guard beside `tuple_visiting`; here that
//! guard is a thread-local stack ([`CLOSURE_VISITING`]), so no line of the
//! verbatim recursion moves, and the `Ty::Closure` arm is the arm that
//! recursion carried, with the tuple arm's checks over CAPTURE order.
//!
//! The v68 nominal item leaf independently scans actual function declarations
//! and signature rows before granting its zero-byte layout.
#![allow(clippy::all)]

use std::cell::RefCell;
use std::collections::BTreeMap;
use trust_ir::ty::{EnumDef, EnumTagRepr, EnumVariant, Ty};
use trust_ir::value::{ClosureTyId, EnumId, RecordId, StructId, TyId};
use trust_ir::{
    EnumLayoutShape, FieldOffsetShape, LayoutError, Module, PointerLayoutShape, TyLayoutKind,
    TyLayoutShape, TyShape,
};

pub fn ty_layout_shape(m: &Module, ty: &Ty) -> Result<TyLayoutShape, LayoutError> {
    ty_layout_shape_inner(
        m,
        ty,
        &mut Vec::new(),
        &mut Vec::new(),
        &mut Vec::new(),
        &mut Vec::new(),
    )
}

/// [`Module::ty_layout_shape`] with the enum cycle guard threaded through:
/// `enum_visiting` tracks the enum ids currently being laid out, so a
/// self-referential enum (an inline `Ty::Enum` cycle not broken by a
/// pointer) fails closed with [`LayoutError::EnumLayoutUnavailable`]
/// instead of recursing without bound.
fn ty_layout_shape_inner(
    m: &Module,
    ty: &Ty,
    enum_visiting: &mut Vec<EnumId>,
    struct_visiting: &mut Vec<StructId>,
    ty_visiting: &mut Vec<TyId>,
    tuple_visiting: &mut Vec<TyId>,
) -> Result<TyLayoutShape, LayoutError> {
    if ty_uses_scalar_layout_table(ty) && !m.target_has_canonical_scalar_layout() {
        return Err(LayoutError::TargetScalarLayoutUnavailable {
            triple: m
                .target_info
                .as_ref()
                .map_or_else(String::new, |target| target.triple.clone()),
        });
    }
    let pointer_bits = m.pointer_bits();
    match ty {
        Ty::Bool => Ok(scalar_layout(TyShape::Bool, 8, Some(8))),
        Ty::I8 => Ok(scalar_layout(
            TyShape::Int {
                signed: true,
                bits: 8,
            },
            8,
            Some(8),
        )),
        Ty::I16 => Ok(scalar_layout(
            TyShape::Int {
                signed: true,
                bits: 16,
            },
            16,
            Some(16),
        )),
        Ty::I32 => Ok(scalar_layout(
            TyShape::Int {
                signed: true,
                bits: 32,
            },
            32,
            Some(32),
        )),
        Ty::I64 => Ok(scalar_layout(
            TyShape::Int {
                signed: true,
                bits: 64,
            },
            64,
            Some(64),
        )),
        Ty::I128 => Ok(scalar_layout(
            TyShape::Int {
                signed: true,
                bits: 128,
            },
            128,
            Some(128),
        )),
        Ty::U8 => Ok(scalar_layout(
            TyShape::Int {
                signed: false,
                bits: 8,
            },
            8,
            Some(8),
        )),
        Ty::U16 => Ok(scalar_layout(
            TyShape::Int {
                signed: false,
                bits: 16,
            },
            16,
            Some(16),
        )),
        Ty::U32 => Ok(scalar_layout(
            TyShape::Int {
                signed: false,
                bits: 32,
            },
            32,
            Some(32),
        )),
        Ty::U64 => Ok(scalar_layout(
            TyShape::Int {
                signed: false,
                bits: 64,
            },
            64,
            Some(64),
        )),
        Ty::U128 => Ok(scalar_layout(
            TyShape::Int {
                signed: false,
                bits: 128,
            },
            128,
            Some(128),
        )),
        // v25 B1 scalars: pointer-width ints take the target's pointer
        // width; char is a 32-bit scalar; Error has NO layout (typing
        // hole - fail closed).
        Ty::Isize => Ok(scalar_layout(
            TyShape::PointerInt { signed: true },
            u64::from(pointer_bits),
            Some(u64::from(pointer_bits)),
        )),
        Ty::Usize => Ok(scalar_layout(
            TyShape::PointerInt { signed: false },
            u64::from(pointer_bits),
            Some(u64::from(pointer_bits)),
        )),
        Ty::Char => Ok(scalar_layout(
            TyShape::Int {
                signed: false,
                bits: 32,
            },
            32,
            Some(32),
        )),
        Ty::Error => Err(LayoutError::UnsupportedTyShape(TyShape::Error)),
        Ty::Dialect(_) => Err(LayoutError::UnsupportedTyShape(TyShape::Dialect)),
        // v43: a handle is one pointer-sized SCALAR word. Deliberately not
        // `TyLayoutKind::ThinPointer` — the layout says how many bytes it
        // occupies, never that anything may address through it.
        Ty::Handle(_) => Ok(scalar_layout(
            TyShape::Handle,
            u64::from(pointer_bits),
            Some(u64::from(pointer_bits)),
        )),
        Ty::F16 => Ok(scalar_layout(TyShape::Float { bits: 16 }, 16, Some(16))),
        Ty::F32 => Ok(scalar_layout(TyShape::Float { bits: 32 }, 32, Some(32))),
        Ty::F64 => Ok(scalar_layout(TyShape::Float { bits: 64 }, 64, Some(64))),
        Ty::Ptr
        | Ty::Ref(_)
        | Ty::RefMut(_)
        | Ty::PtrConst(_)
        | Ty::PtrMut(_)
        | Ty::Rc(_)
        | Ty::Func(_) => Ok(TyLayoutShape {
            size_bits: u64::from(pointer_bits),
            align_bits: Some(u64::from(pointer_bits)),
            kind: TyLayoutKind::ThinPointer,
        }),
        Ty::FnItem(id) => {
            let bad = || LayoutError::UnsupportedTyShape(TyShape::FnItem);
            let mut matching = m.functions.iter().filter(|function| function.id == *id);
            let function = matching.next().ok_or_else(bad)?;
            if matching.next().is_some() || m.func_types.get(function.ty.as_usize()).is_none() {
                return Err(bad());
            }
            Ok(TyLayoutShape {
                size_bits: 0,
                align_bits: Some(8),
                kind: TyLayoutKind::FnItem,
            })
        }
        Ty::FatPtr(kind) => {
            let ptr = PointerLayoutShape::fat(pointer_bits, kind.metadata_shape());
            let size_bits = u64::from(ptr.total_bits().ok_or(LayoutError::SizeOverflow)?);
            Ok(TyLayoutShape {
                size_bits,
                align_bits: Some(u64::from(pointer_bits)),
                kind: TyLayoutKind::FatPointer(kind.metadata_shape()),
            })
        }
        Ty::Unit => Ok(TyLayoutShape {
            size_bits: 0,
            align_bits: Some(8),
            kind: TyLayoutKind::Unit,
        }),
        Ty::Never => Ok(TyLayoutShape {
            size_bits: 0,
            align_bits: None,
            kind: TyLayoutKind::Never,
        }),
        Ty::Struct(id) => {
            if struct_visiting.contains(id) {
                // A direct, inline struct cycle has no finite layout. Pointers do
                // not recurse through this path, so ordinary recursive Rust data
                // structures remain representable.
                return Err(LayoutError::StructLayoutIncoherent(*id));
            }
            let sd = m
                .structs
                .iter()
                .find(|sd| sd.id == *id)
                .ok_or(LayoutError::MissingStruct(*id))?;
            let size = sd.size.ok_or(LayoutError::MissingStructSize(*id))?;
            let align = sd.align.ok_or(LayoutError::MissingStructAlign(*id))?;
            if align == 0 || !align.is_power_of_two() || !size.is_multiple_of(align) {
                return Err(LayoutError::StructLayoutIncoherent(*id));
            }
            let clamp = match sd.repr {
                trust_ir::ty::StructRepr::Packed(packed)
                    if packed != 0 && packed.is_power_of_two() =>
                {
                    u64::from(packed)
                }
                trust_ir::ty::StructRepr::Packed(_) => {
                    return Err(LayoutError::StructLayoutIncoherent(*id));
                }
                _ => u64::MAX,
            };
            if align > clamp {
                return Err(LayoutError::StructLayoutIncoherent(*id));
            }

            struct_visiting.push(*id);
            let result = (|| {
                let mut ranges = Vec::with_capacity(sd.fields.len());
                let mut fields = Vec::with_capacity(sd.fields.len());
                let mut transparent_carrier = None;
                let mut transparent_nontrivial = 0usize;
                for (field, def) in sd.fields.iter().enumerate() {
                    let field_layout = ty_layout_shape_inner(
                        m,
                        &def.ty,
                        enum_visiting,
                        struct_visiting,
                        ty_visiting,
                        tuple_visiting,
                    )?;
                    let field_size = field_layout
                        .size_bytes()
                        .ok_or(LayoutError::StructLayoutIncoherent(*id))?;
                    let field_align = field_layout
                        .align_bits
                        .filter(|bits| *bits != 0 && bits.is_multiple_of(8))
                        .map(|bits| bits / 8)
                        .ok_or(LayoutError::StructLayoutIncoherent(*id))?
                        .max(1)
                        .min(clamp);
                    let offset = match def.offset {
                        Some(offset) => offset,
                        None if field_size == 0 => 0,
                        None => {
                            return Err(LayoutError::MissingFieldOffset {
                                struct_id: *id,
                                field: field as u32,
                            });
                        }
                    };
                    if !offset.is_multiple_of(field_align)
                        || field_align > align
                        || offset.checked_add(field_size).is_none_or(|end| end > size)
                    {
                        return Err(LayoutError::StructLayoutIncoherent(*id));
                    }
                    if sd.repr == trust_ir::ty::StructRepr::Transparent
                        && (field_size != 0 || field_align != 1)
                    {
                        transparent_nontrivial += 1;
                        transparent_carrier = Some((field_size, field_align, offset));
                    }
                    ranges.push((offset, field_size));
                    fields.push(FieldOffsetShape {
                        field: field as u32,
                        name: def.name.clone(),
                        ty_shape: def.ty.shape(),
                        // A missing offset is information-free only for a ZST;
                        // canonicalize that placement to byte zero for consumers.
                        offset_bits: Some(offset.checked_mul(8).ok_or(LayoutError::SizeOverflow)?),
                    });
                }
                for left in 0..ranges.len() {
                    for right in left + 1..ranges.len() {
                        if byte_ranges_overlap(
                            ranges[left].0,
                            ranges[left].1,
                            ranges[right].0,
                            ranges[right].1,
                        ) {
                            return Err(LayoutError::StructLayoutIncoherent(*id));
                        }
                    }
                }
                if sd.repr == trust_ir::ty::StructRepr::Transparent {
                    // rustc's transparent rule is about 1-ZSTs, not size
                    // alone. A zero-sized field with alignment > 1 is the
                    // representation-bearing field. The wrapper must match
                    // that sole carrier exactly (including offset zero); if
                    // every field is a 1-ZST, the wrapper itself is a 1-ZST.
                    let (carrier_size, carrier_align, carrier_offset) =
                        transparent_carrier.unwrap_or((0, 1, 0));
                    if transparent_nontrivial > 1
                        || size != carrier_size
                        || align != carrier_align
                        || carrier_offset != 0
                    {
                        return Err(LayoutError::StructLayoutIncoherent(*id));
                    }
                }
                Ok(TyLayoutShape {
                    size_bits: size.checked_mul(8).ok_or(LayoutError::SizeOverflow)?,
                    align_bits: Some(align.checked_mul(8).ok_or(LayoutError::SizeOverflow)?),
                    kind: TyLayoutKind::Struct { id: *id, fields },
                })
            })();
            struct_visiting.pop();
            result
        }
        Ty::Array(elem, len) => {
            if ty_visiting.contains(elem) {
                return Err(LayoutError::TyLayoutCycle(*elem));
            }
            let elem_ty = m
                .types
                .get(elem.as_usize())
                .ok_or(LayoutError::MissingType(*elem))?;
            ty_visiting.push(*elem);
            let elem_layout = ty_layout_shape_inner(
                m,
                elem_ty,
                enum_visiting,
                struct_visiting,
                ty_visiting,
                tuple_visiting,
            );
            ty_visiting.pop();
            let elem_layout = elem_layout?;
            Ok(TyLayoutShape {
                size_bits: elem_layout
                    .size_bits
                    .checked_mul(*len)
                    .ok_or(LayoutError::SizeOverflow)?,
                align_bits: elem_layout.align_bits,
                kind: TyLayoutKind::Array {
                    elem: *elem,
                    len: *len,
                    stride_bits: elem_layout.size_bits,
                },
            })
        }
        Ty::Vector(elem, lanes) => {
            let elem_layout = ty_layout_shape_inner(
                m,
                elem,
                enum_visiting,
                struct_visiting,
                ty_visiting,
                tuple_visiting,
            )?;
            Ok(TyLayoutShape {
                size_bits: elem_layout
                    .size_bits
                    .checked_mul(u64::from(*lanes))
                    .ok_or(LayoutError::SizeOverflow)?,
                align_bits: elem_layout.align_bits,
                kind: TyLayoutKind::Vector {
                    elem_shape: elem.shape(),
                    lanes: *lanes,
                    lane_bits: elem_layout.size_bits,
                },
            })
        }
        // trust-ir's CANONICAL tagged-union layout (see
        // `Module::enum_layout_shape`). Deliberately NOT a claim of rustc
        // layout parity: no niche optimization, no variant reordering.
        Ty::Enum(id) => {
            let layout = enum_layout_shape_inner(
                m,
                *id,
                enum_visiting,
                struct_visiting,
                ty_visiting,
                tuple_visiting,
            )?;
            Ok(TyLayoutShape {
                size_bits: layout.size_bits,
                align_bits: Some(layout.align_bits),
                kind: TyLayoutKind::Enum {
                    id: *id,
                    variants: layout.discriminants.len(),
                },
            })
        }
        Ty::Tuple(elems) => {
            let Some(desc) = tuple_layout_descriptor(m, ty)? else {
                return if elems.is_empty() {
                    Ok(TyLayoutShape {
                        size_bits: 0,
                        align_bits: Some(8),
                        kind: TyLayoutKind::Unit,
                    })
                } else {
                    Err(LayoutError::UnsupportedTyShape(ty.shape()))
                };
            };
            let bad = || LayoutError::TupleLayoutIncoherent(desc.tuple_type);
            if m.target_info.is_none() {
                return Err(LayoutError::TupleLayoutTargetMissing);
            }
            if tuple_visiting.contains(&desc.tuple_type)
                || desc.align == 0
                || !desc.align.is_power_of_two()
                || !desc.size.is_multiple_of(desc.align)
                || desc.field_offsets.len() != elems.len()
            {
                return Err(bad());
            }
            tuple_visiting.push(desc.tuple_type);
            let result = (|| {
                let mut fields = Vec::with_capacity(elems.len());
                let mut ranges = Vec::with_capacity(elems.len());
                for (index, (elem, offset)) in elems.iter().zip(&desc.field_offsets).enumerate() {
                    let layout = ty_layout_shape_inner(
                        m,
                        elem,
                        enum_visiting,
                        struct_visiting,
                        ty_visiting,
                        tuple_visiting,
                    )?;
                    let size = layout.size_bytes().ok_or_else(bad)?;
                    let align = layout
                        .align_bits
                        .filter(|bits| *bits != 0 && bits.is_multiple_of(8))
                        .map(|bits| bits / 8)
                        .ok_or_else(bad)?;
                    if align > desc.align
                        || !offset.is_multiple_of(align)
                        || offset.checked_add(size).is_none_or(|end| end > desc.size)
                    {
                        return Err(bad());
                    }
                    ranges.push((*offset, size));
                    fields.push(FieldOffsetShape {
                        field: u32::try_from(index).map_err(|_| bad())?,
                        name: index.to_string(),
                        ty_shape: elem.shape(),
                        offset_bits: Some(offset.checked_mul(8).ok_or(LayoutError::SizeOverflow)?),
                    });
                }
                for left in 0..ranges.len() {
                    for right in left + 1..ranges.len() {
                        if byte_ranges_overlap(
                            ranges[left].0,
                            ranges[left].1,
                            ranges[right].0,
                            ranges[right].1,
                        ) {
                            return Err(bad());
                        }
                    }
                }
                Ok(TyLayoutShape {
                    size_bits: desc.size.checked_mul(8).ok_or(LayoutError::SizeOverflow)?,
                    align_bits: Some(desc.align.checked_mul(8).ok_or(LayoutError::SizeOverflow)?),
                    kind: TyLayoutKind::Tuple { fields },
                })
            })();
            tuple_visiting.pop();
            result
        }
        // REPRESENTATION PRESERVATION, enforced here: a `Refine(b, p)`
        // lays out EXACTLY as `b` does. This delegation is what makes the
        // whole typed-value-model change unable to move a byte of any
        // downstream artifact.
        Ty::Refine(base, _) => match m.types.get(base.as_usize()) {
            Some(_) if ty_visiting.contains(base) => Err(LayoutError::TyLayoutCycle(*base)),
            Some(base_ty) => {
                ty_visiting.push(*base);
                let result = ty_layout_shape_inner(
                    m,
                    base_ty,
                    enum_visiting,
                    struct_visiting,
                    ty_visiting,
                    tuple_visiting,
                );
                ty_visiting.pop();
                result
            }
            None => Err(LayoutError::UnsupportedTyShape(TyShape::Refine)),
        },
        // v58: a closure type has a byte image exactly when the producer
        // DECLARED one. Absence is the pre-v58 state and stays
        // `UnsupportedTyShape` — never a guessed declaration-order frame.
        Ty::Closure(id) => {
            let Some(desc) = closure_layout_descriptor(m, *id)? else {
                return Err(LayoutError::UnsupportedTyShape(ty.shape()));
            };
            let bad = || LayoutError::ClosureLayoutIncoherent(desc.closure);
            if m.target_info.is_none() {
                return Err(LayoutError::ClosureLayoutTargetMissing);
            }
            let captures = m.closure_type(*id).ok_or_else(bad)?.captures.clone();
            // A closure that captures a value of its own type (directly, or
            // through an aggregate no pointer breaks) has no finite frame.
            if CLOSURE_VISITING.with(|visiting| visiting.borrow().contains(id))
                || desc.align == 0
                || !desc.align.is_power_of_two()
                || !desc.size.is_multiple_of(desc.align)
                || desc.capture_offsets.len() != captures.len()
            {
                return Err(bad());
            }
            CLOSURE_VISITING.with(|visiting| visiting.borrow_mut().push(*id));
            let result = (|| {
                let mut fields = Vec::with_capacity(captures.len());
                let mut ranges = Vec::with_capacity(captures.len());
                for (index, (capture, offset)) in
                    captures.iter().zip(&desc.capture_offsets).enumerate()
                {
                    let layout = ty_layout_shape_inner(
                        m,
                        capture,
                        enum_visiting,
                        struct_visiting,
                        ty_visiting,
                        tuple_visiting,
                    )?;
                    let size = layout.size_bytes().ok_or_else(bad)?;
                    let align = layout
                        .align_bits
                        .filter(|bits| *bits != 0 && bits.is_multiple_of(8))
                        .map(|bits| bits / 8)
                        .ok_or_else(bad)?;
                    if align > desc.align
                        || !offset.is_multiple_of(align)
                        || offset.checked_add(size).is_none_or(|end| end > desc.size)
                    {
                        return Err(bad());
                    }
                    ranges.push((*offset, size));
                    fields.push(FieldOffsetShape {
                        field: u32::try_from(index).map_err(|_| bad())?,
                        name: index.to_string(),
                        ty_shape: capture.shape(),
                        offset_bits: Some(offset.checked_mul(8).ok_or(LayoutError::SizeOverflow)?),
                    });
                }
                for left in 0..ranges.len() {
                    for right in left + 1..ranges.len() {
                        if byte_ranges_overlap(
                            ranges[left].0,
                            ranges[left].1,
                            ranges[right].0,
                            ranges[right].1,
                        ) {
                            return Err(bad());
                        }
                    }
                }
                Ok(TyLayoutShape {
                    size_bits: desc.size.checked_mul(8).ok_or(LayoutError::SizeOverflow)?,
                    align_bits: Some(desc.align.checked_mul(8).ok_or(LayoutError::SizeOverflow)?),
                    kind: TyLayoutKind::Closure {
                        id: *id,
                        captures: fields,
                    },
                })
            })();
            CLOSURE_VISITING.with(|visiting| visiting.borrow_mut().pop());
            result
        }
        // A tensor has no memory layout (the tensor region, PKG-U13a): its
        // extents are run-time values, as a sequence's length is.
        Ty::Set(_, _) | Ty::Sequence(_) | Ty::Record(_) | Ty::Tensor(_, _) => {
            Err(LayoutError::UnsupportedTyShape(ty.shape()))
        }
        Ty::Storage(layout) => {
            let size = layout.size_bytes;
            let align = layout.align_bytes;
            let bad = || LayoutError::UnsupportedTyShape(TyShape::Storage);
            if align == 0
                || align.count_ones() != 1
                || !size.is_multiple_of(align)
                || !matches!(pointer_bits, 32 | 64)
                || (pointer_bits == 32 && (size >= (1_u64 << 32) || align > (1_u64 << 31)))
            {
                return Err(bad());
            }
            Ok(TyLayoutShape {
                size_bits: size.checked_mul(8).ok_or_else(bad)?,
                align_bits: Some(align.checked_mul(8).ok_or_else(bad)?),
                kind: TyLayoutKind::Storage,
            })
        }
        Ty::Ext(e) => e.unreachable(),
    }
}

thread_local! {
    /// The closure types the recursion is laying out (the `closure_visiting`
    /// guard of the recursion v58 was written for, threaded out of band).
    static CLOSURE_VISITING: RefCell<Vec<ClosureTyId>> = const { RefCell::new(Vec::new()) };
}

pub fn enum_layout_shape(m: &Module, id: EnumId) -> Result<EnumLayoutShape, LayoutError> {
    enum_layout_shape_inner(
        m,
        id,
        &mut Vec::new(),
        &mut Vec::new(),
        &mut Vec::new(),
        &mut Vec::new(),
    )
}

/// [`Module::enum_layout_shape`] with the shared enum cycle guard.
fn enum_layout_shape_inner(
    m: &Module,
    id: EnumId,
    enum_visiting: &mut Vec<EnumId>,
    struct_visiting: &mut Vec<StructId>,
    ty_visiting: &mut Vec<TyId>,
    tuple_visiting: &mut Vec<TyId>,
) -> Result<EnumLayoutShape, LayoutError> {
    if enum_visiting.contains(&id) {
        // Inline self-reference (not broken by a pointer): no finite
        // canonical layout exists.
        return Err(LayoutError::EnumLayoutUnavailable(id));
    }
    let ed = m
        .enums
        .iter()
        .find(|ed| ed.id == id)
        .ok_or(LayoutError::EnumLayoutUnavailable(id))?;
    let discriminants =
        effective_discriminants(ed).ok_or(LayoutError::EnumLayoutUnavailable(id))?;
    let tag = canonical_tag_repr(ed).ok_or(LayoutError::EnumLayoutUnavailable(id))?;
    let tag_size_bits = tag.size_bytes() * 8;
    // WS2.22 (review): a lane's ALIGNMENT is the target's for the lane
    // type — asked of the layout authority, as the reference interpreter
    // asks `byte_align_in` for the same number — never the byte count. The
    // ask is made for exactly the lane that EXISTS, the same `lane_repr`
    // the validator computes: the canonical tag when no descriptor is
    // declared (the canonical layout stores it, and its alignment enters
    // `max(tag alignment, payload alignment)` — a fieldless enum has no
    // field to draw the scalar-table refusal, and its tag is a scalar of
    // exactly the kind the table is about), the placed tag under `Direct`,
    // the niche type under `Niche`, and nothing under `Untagged`, which
    // stores no lane. On a target with no scalar table the ask propagates
    // `TargetScalarLayoutUnavailable`: the layout is unjudgeable, not
    // admissible.
    let lane_align_bits = match ed.layout.as_ref().map(|desc| &desc.encoding) {
        None
        | Some(trust_ir::ty::EnumTagEncoding::Direct { .. })
        | Some(trust_ir::ty::EnumTagEncoding::DirectWithUninhabited { .. }) => {
            Some(enum_tag_repr_align(m, tag)? * 8)
        }
        Some(trust_ir::ty::EnumTagEncoding::Niche { niche_ty, .. }) => {
            Some(enum_tag_repr_align(m, *niche_ty)? * 8)
        }
        Some(
            trust_ir::ty::EnumTagEncoding::Untagged
            | trust_ir::ty::EnumTagEncoding::SingleInhabited { .. },
        ) => None,
    };

    enum_visiting.push(id);
    let result = (|| {
        // Payload region: each variant laid out C-style; the region takes
        // the max variant size and max variant alignment (min 1 byte).
        let mut payload_size_bits: u64 = 0;
        let mut payload_align_bits: u64 = 8;
        let mut variant_field_sizes = Vec::with_capacity(ed.variants.len());
        let mut variant_field_aligns = Vec::with_capacity(ed.variants.len());
        let mut never_field = false;
        let profiles = match ed.layout.as_ref().map(|d| &d.encoding) {
            Some(trust_ir::ty::EnumTagEncoding::DirectWithUninhabited {
                tag_offset,
                variants,
            }) => {
                let desc = ed.layout.as_ref().unwrap();
                let dead = least_fixpoint(m);
                let expected: Vec<_> = ed
                    .variants
                    .iter()
                    .enumerate()
                    .filter(|(_, row)| dead.variant_is_uninhabited(row))
                    .map(|(i, _)| i)
                    .collect();
                if !source_references_exist(m, ed.variants.iter().flat_map(|v| &v.fields))
                    || expected.len() != variants.len()
                    || variants
                        .iter()
                        .zip(expected)
                        .any(|(row, i)| row.variant as usize != i)
                    || desc.align == 0
                    || !desc.align.is_power_of_two()
                    || !desc.size.is_multiple_of(desc.align)
                    || desc.variant_field_offsets.len() != ed.variants.len()
                {
                    return Err(LayoutError::EnumLayoutUnavailable(id));
                }
                let tag_size = tag_size_bits / 8;
                let tag_align = lane_align_bits.unwrap() / 8;
                for row in variants {
                    let source = &ed.variants[row.variant as usize];
                    let offsets = &desc.variant_field_offsets[row.variant as usize];
                    if row.align == 0
                        || !row.align.is_power_of_two()
                        || !row.size.is_multiple_of(row.align)
                        || row.size > desc.size
                        || row.align > desc.align
                        || row.fields.len() != source.fields.len()
                        || offsets.len() != source.fields.len()
                        || tag_align > row.align
                        || !tag_offset.is_multiple_of(tag_align)
                        || tag_offset
                            .checked_add(tag_size)
                            .is_none_or(|end| end > row.size)
                    {
                        return Err(LayoutError::EnumLayoutUnavailable(id));
                    }
                    for (i, (field, offset)) in row.fields.iter().zip(offsets).enumerate() {
                        if field.align == 0
                            || !field.align.is_power_of_two()
                            || !field.size.is_multiple_of(field.align)
                            || field.align > row.align
                            || !offset.is_multiple_of(field.align)
                            || offset
                                .checked_add(field.size)
                                .is_none_or(|end| end > row.size)
                            || byte_ranges_overlap(*tag_offset, tag_size, *offset, field.size)
                            || row.fields[..i]
                                .iter()
                                .zip(&offsets[..i])
                                .any(|(prior, pos)| {
                                    byte_ranges_overlap(*pos, prior.size, *offset, field.size)
                                })
                        {
                            return Err(LayoutError::EnumLayoutUnavailable(id));
                        }
                    }
                }
                variants.as_slice()
            }
            _ => &[],
        };
        // Dead payload storage can be omitted only after checking the whole
        // declared reference graph and the independently computed least fixpoint.
        let single =
            match ed.layout.as_ref().map(|d| &d.encoding) {
                Some(trust_ir::ty::EnumTagEncoding::SingleInhabited { variant }) => {
                    let selected = usize::try_from(*variant)
                        .map_err(|_| LayoutError::EnumLayoutUnavailable(id))?;
                    let dead = least_fixpoint(m);
                    if selected >= ed.variants.len()
                        || !source_references_exist(m, ed.variants.iter().flat_map(|v| &v.fields))
                        || ed.variants.iter().enumerate().any(|(index, row)| {
                            dead.variant_is_uninhabited(row) != (index != selected)
                        })
                    {
                        return Err(LayoutError::EnumLayoutUnavailable(id));
                    }
                    Some(selected)
                }
                _ => None,
            };
        for (index, variant) in ed.variants.iter().enumerate() {
            if let Some(profile) = profiles.iter().find(|row| row.variant as usize == index) {
                let mut end = 0;
                let mut align = 8;
                for field in &profile.fields {
                    let field_align = field
                        .align
                        .checked_mul(8)
                        .ok_or(LayoutError::SizeOverflow)?;
                    let field_size = field.size.checked_mul(8).ok_or(LayoutError::SizeOverflow)?;
                    end = align_up_bits(end, field_align)?
                        .checked_add(field_size)
                        .ok_or(LayoutError::SizeOverflow)?;
                    align = align.max(field_align);
                }
                payload_size_bits = payload_size_bits.max(align_up_bits(end, align)?);
                payload_align_bits = payload_align_bits.max(align);
                variant_field_sizes.push(profile.fields.iter().map(|f| f.size).collect());
                variant_field_aligns.push(profile.fields.iter().map(|f| f.align).collect());
                continue;
            }
            if single.is_some_and(|selected| index != selected) {
                variant_field_sizes.push(Vec::new());
                variant_field_aligns.push(Vec::new());
                continue;
            }
            let mut offset_bits: u64 = 0;
            let mut variant_align_bits: u64 = 8;
            let mut field_sizes = Vec::with_capacity(variant.fields.len());
            let mut field_aligns = Vec::with_capacity(variant.fields.len());
            for field_ty in &variant.fields {
                let field_layout = ty_layout_shape_inner(
                    m,
                    field_ty,
                    enum_visiting,
                    struct_visiting,
                    ty_visiting,
                    tuple_visiting,
                )?;
                let field_size = field_layout
                    .size_bytes()
                    .ok_or(LayoutError::EnumLayoutUnavailable(id))?;
                // WS3.14: a `!` payload field (rustc's `B(!)`) occupies no
                // bytes and — as in rustc, where `!` is size 0 / align 1 —
                // constrains no offset. `Ty::Never` has no alignment of its
                // own, so it is admitted here ONLY under a producer
                // descriptor (checked after the loop); the canonical layout
                // keeps refusing an enum that spells one.
                let field_align_bits = if matches!(field_ty, Ty::Never) {
                    never_field = true;
                    8
                } else {
                    field_layout
                        .align_bits
                        .ok_or(LayoutError::EnumLayoutUnavailable(id))?
                        .max(8)
                };
                offset_bits = align_up_bits(offset_bits, field_align_bits)?;
                offset_bits = offset_bits
                    .checked_add(field_layout.size_bits)
                    .ok_or(LayoutError::SizeOverflow)?;
                variant_align_bits = variant_align_bits.max(field_align_bits);
                field_sizes.push(field_size);
                field_aligns.push(field_align_bits / 8);
            }
            let variant_size_bits = align_up_bits(offset_bits, variant_align_bits)?;
            payload_size_bits = payload_size_bits.max(variant_size_bits);
            payload_align_bits = payload_align_bits.max(variant_align_bits);
            variant_field_sizes.push(field_sizes);
            variant_field_aligns.push(field_aligns);
        }
        if never_field && ed.layout.is_none() {
            return Err(LayoutError::EnumLayoutUnavailable(id));
        }

        let payload_offset_bits = align_up_bits(tag_size_bits, payload_align_bits)?;
        // The canonical image — tag lane at 0, payload after it, alignment
        // the max of the two — is formed only when no descriptor replaces
        // it: a declared descriptor's size and align are normative, and
        // under `Niche` / `Untagged` there is no canonical tag lane whose
        // alignment could have been asked for.
        let (size_bits, align_bits) = if let Some(desc) = &ed.layout {
            if desc.align == 0
                || !desc.align.is_power_of_two()
                || !desc.size.is_multiple_of(desc.align)
                || desc.variant_field_offsets.len() != ed.variants.len()
            {
                return Err(LayoutError::EnumLayoutUnavailable(id));
            }
            for ((offsets, sizes), aligns) in desc
                .variant_field_offsets
                .iter()
                .zip(&variant_field_sizes)
                .zip(&variant_field_aligns)
            {
                if offsets.len() != sizes.len() || offsets.len() != aligns.len() {
                    return Err(LayoutError::EnumLayoutUnavailable(id));
                }
                for ((offset, field_size), field_align) in offsets.iter().zip(sizes).zip(aligns) {
                    if !offset.is_multiple_of(*field_align)
                        || *field_align > desc.align
                        || offset
                            .checked_add(*field_size)
                            .is_none_or(|end| end > desc.size)
                    {
                        return Err(LayoutError::EnumLayoutUnavailable(id));
                    }
                }
                for left in 0..offsets.len() {
                    for right in left + 1..offsets.len() {
                        if byte_ranges_overlap(
                            offsets[left],
                            sizes[left],
                            offsets[right],
                            sizes[right],
                        ) {
                            return Err(LayoutError::EnumLayoutUnavailable(id));
                        }
                    }
                }
            }
            match &desc.encoding {
                // v37: no tag lane exists, so every tag-PLACEMENT check is
                // vacuous — there is no offset to align, nothing to fit
                // inside `desc.size`, and nothing that could overlap a
                // payload field. The per-field bound above still ran and is
                // what makes this encoding safe: the fields must lie inside
                // the declared size exactly as for the tagged encodings.
                //
                // The one check with content is that a variant is
                // RECOVERABLE without reading anything, which holds exactly
                // when there is one. This mirrors the interpreter and the
                // validator: all three must agree, or a shape query would
                // report a size for an enum the interpreter refuses to load.
                trust_ir::ty::EnumTagEncoding::Untagged => {
                    if ed.variants.len() != 1 {
                        return Err(LayoutError::EnumLayoutUnavailable(id));
                    }
                }
                trust_ir::ty::EnumTagEncoding::SingleInhabited { .. } => {}
                trust_ir::ty::EnumTagEncoding::Direct { tag_offset }
                | trust_ir::ty::EnumTagEncoding::DirectWithUninhabited { tag_offset, .. } => {
                    let tag_size = tag_size_bits / 8;
                    // WS2.22: the tag's PLACEMENT is judged against the
                    // target's alignment for the tag type (asked of the
                    // layout authority above, never reused from the byte
                    // count). On a target with no scalar table that ask
                    // already propagated `TargetScalarLayoutUnavailable`
                    // — the descriptor is unjudgeable, not admissible.
                    let tag_align =
                        lane_align_bits.ok_or(LayoutError::EnumLayoutUnavailable(id))? / 8;
                    if tag_align > desc.align
                        || !tag_offset.is_multiple_of(tag_align)
                        || tag_offset
                            .checked_add(tag_size)
                            .is_none_or(|end| end > desc.size)
                    {
                        return Err(LayoutError::EnumLayoutUnavailable(id));
                    }
                    for (offsets, sizes) in
                        desc.variant_field_offsets.iter().zip(&variant_field_sizes)
                    {
                        if offsets.iter().zip(sizes).any(|(offset, field_size)| {
                            byte_ranges_overlap(*tag_offset, tag_size, *offset, *field_size)
                        }) {
                            return Err(LayoutError::EnumLayoutUnavailable(id));
                        }
                    }
                }
                trust_ir::ty::EnumTagEncoding::Niche {
                    untagged_variant,
                    niche_variants_start,
                    niche_variants_end,
                    niche_start,
                    niche_offset,
                    niche_ty,
                } => {
                    let variant_count = u32::try_from(ed.variants.len())
                        .map_err(|_| LayoutError::EnumLayoutUnavailable(id))?;
                    let niche_size = niche_ty.size_bytes();
                    // WS2.22: as for the direct tag, the niche lane's
                    // alignment is the target's for the lane type (asked
                    // above).
                    let niche_align =
                        lane_align_bits.ok_or(LayoutError::EnumLayoutUnavailable(id))? / 8;
                    let niche_bits = u32::try_from(niche_size * 8)
                        .map_err(|_| LayoutError::EnumLayoutUnavailable(id))?;
                    let niche_mask = match niche_bits {
                        0 => return Err(LayoutError::EnumLayoutUnavailable(id)),
                        128 => u128::MAX,
                        bits if bits < 128 => (1u128 << bits) - 1,
                        _ => return Err(LayoutError::EnumLayoutUnavailable(id)),
                    };
                    let niche_span = niche_variants_end
                        .checked_sub(*niche_variants_start)
                        .map(u128::from)
                        .ok_or(LayoutError::EnumLayoutUnavailable(id))?;
                    // WS3.14: every INHABITED variant is the untagged one
                    // or lies in the niche interval; an uninhabited variant
                    // (rustc's `B(!)`) needs no encoding and may lie in
                    // either place or in neither. The same rule, through the
                    // same helper, as the validator and the interpreter.
                    if *untagged_variant >= variant_count
                        || *niche_variants_end >= variant_count
                        || niche_unencoded_inhabited_variant(
                            m,
                            ed,
                            *untagged_variant,
                            *niche_variants_start,
                            *niche_variants_end,
                        )
                        .is_some()
                        || niche_span > niche_mask
                        || *niche_start > niche_mask
                        || niche_align > desc.align
                        || !niche_offset.is_multiple_of(niche_align)
                        || niche_offset
                            .checked_add(niche_size)
                            .is_none_or(|end| end > desc.size)
                    {
                        return Err(LayoutError::EnumLayoutUnavailable(id));
                    }
                    let untagged = *untagged_variant as usize;
                    let lane_end = niche_offset
                        .checked_add(niche_size)
                        .ok_or(LayoutError::EnumLayoutUnavailable(id))?;
                    let lane_is_covered = desc.variant_field_offsets[untagged]
                        .iter()
                        .zip(&variant_field_sizes[untagged])
                        .any(|(field_offset, field_size)| {
                            *field_size > 0
                                && *field_offset <= *niche_offset
                                && field_offset
                                    .checked_add(*field_size)
                                    .is_some_and(|field_end| field_end >= lane_end)
                        });
                    if !lane_is_covered {
                        return Err(LayoutError::EnumLayoutUnavailable(id));
                    }
                    for variant in *niche_variants_start..=*niche_variants_end {
                        if variant == *untagged_variant {
                            continue;
                        }
                        let variant = variant as usize;
                        if desc.variant_field_offsets[variant]
                            .iter()
                            .zip(&variant_field_sizes[variant])
                            .any(|(field_offset, field_size)| {
                                byte_ranges_overlap(
                                    *niche_offset,
                                    niche_size,
                                    *field_offset,
                                    *field_size,
                                )
                            })
                        {
                            return Err(LayoutError::EnumLayoutUnavailable(id));
                        }
                    }
                }
            }
            (
                desc.size.checked_mul(8).ok_or(LayoutError::SizeOverflow)?,
                desc.align.checked_mul(8).ok_or(LayoutError::SizeOverflow)?,
            )
        } else {
            // WS2.22 (review): the canonical alignment is
            // `max(tag alignment, payload alignment)` — the tag's the
            // target's, asked above — as the reference interpreter forms
            // it, never `max(tag SIZE, payload alignment)`.
            let tag_align_bits = lane_align_bits.ok_or(LayoutError::EnumLayoutUnavailable(id))?;
            let align_bits = tag_align_bits.max(payload_align_bits);
            let size_bits = align_up_bits(
                payload_offset_bits
                    .checked_add(payload_size_bits)
                    .ok_or(LayoutError::SizeOverflow)?,
                align_bits,
            )?;
            (size_bits, align_bits)
        };
        Ok(EnumLayoutShape {
            id,
            tag,
            tag_size_bits,
            payload_offset_bits,
            payload_size_bits,
            size_bits,
            align_bits,
            discriminants,
            descriptor: ed.layout.clone(),
        })
    })();
    enum_visiting.pop();
    result
}

pub fn enum_tag_repr_align(m: &Module, repr: EnumTagRepr) -> Result<u64, LayoutError> {
    let ty = repr.ty();
    let align_bits = ty_layout_shape(m, &ty)?
        .align_bits
        .filter(|bits| *bits != 0 && bits.is_multiple_of(8))
        .ok_or_else(|| LayoutError::UnsupportedTyShape(ty.shape()))?;
    Ok(align_bits / 8)
}

pub fn struct_field_offset_bits(
    m: &Module,
    struct_id: StructId,
    field: u32,
) -> Result<u64, LayoutError> {
    let layout = ty_layout_shape(m, &Ty::Struct(struct_id))?;
    let TyLayoutKind::Struct { fields, .. } = layout.kind else {
        return Err(LayoutError::StructLayoutIncoherent(struct_id));
    };
    fields
        .get(field as usize)
        .and_then(|field| field.offset_bits)
        .ok_or(LayoutError::MissingFieldOffset { struct_id, field })
}

pub fn effective_discriminants(def: &EnumDef) -> Option<Vec<i128>> {
    let mut out: Vec<i128> = Vec::with_capacity(def.variants.len());
    let mut next: Option<i128> = Some(0);
    for i in 0..def.variants.len() {
        let value = match def.discriminants.get(i).copied().flatten() {
            Some(explicit) => explicit,
            None => next?,
        };
        if out.contains(&value) {
            return None;
        }
        out.push(value);
        next = value.checked_add(1);
    }
    Some(out)
}

pub fn canonical_tag_repr(def: &EnumDef) -> Option<EnumTagRepr> {
    if def.variants.is_empty() {
        return None;
    }
    let discs = effective_discriminants(def)?;
    if let Some(hint) = def.repr {
        return discs.iter().all(|d| hint.fits(*d)).then_some(hint);
    }
    let min = *discs.iter().min()?;
    let max = *discs.iter().max()?;
    EnumTagRepr::smallest_for(min, max)
}

fn ty_uses_scalar_layout_table(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Bool
            | Ty::I8
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
            | Ty::Ptr
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Rc(_)
            | Ty::Func(_)
            | Ty::FatPtr(_)
    )
}

fn scalar_layout(shape: TyShape, size_bits: u64, align_bits: Option<u64>) -> TyLayoutShape {
    TyLayoutShape {
        size_bits,
        align_bits,
        kind: TyLayoutKind::Scalar(shape),
    }
}

fn align_up_bits(offset_bits: u64, align_bits: u64) -> Result<u64, LayoutError> {
    debug_assert!(align_bits > 0, "alignment must be nonzero");
    let rem = offset_bits % align_bits;
    if rem == 0 {
        return Ok(offset_bits);
    }
    offset_bits
        .checked_add(align_bits - rem)
        .ok_or(LayoutError::SizeOverflow)
}

fn byte_ranges_overlap(a_offset: u64, a_size: u64, b_offset: u64, b_size: u64) -> bool {
    if a_size == 0 || b_size == 0 {
        return false;
    }
    let Some(a_end) = a_offset.checked_add(a_size) else {
        return true;
    };
    let Some(b_end) = b_offset.checked_add(b_size) else {
        return true;
    };
    a_offset < b_end && b_offset < a_end
}

/// `Module::tuple_layout_descriptor` (unchanged by the table, copied so the
/// oracle shares none of the crate's layout code).
pub fn tuple_layout_descriptor<'m>(
    m: &'m Module,
    ty: &Ty,
) -> Result<Option<&'m trust_ir::TupleLayoutDescriptor>, LayoutError> {
    let mut found = None;
    for desc in &m.tuple_layouts {
        let declared = m
            .types
            .get(desc.tuple_type.as_usize())
            .ok_or(LayoutError::MissingType(desc.tuple_type))?;
        if !matches!(declared, Ty::Tuple(_)) {
            return Err(LayoutError::TupleLayoutIncoherent(desc.tuple_type));
        }
        if declared == ty {
            if found.is_some() {
                return Err(LayoutError::TupleLayoutIncoherent(desc.tuple_type));
            }
            found = Some(desc);
        }
    }
    Ok(found)
}

/// `Module::closure_layout_descriptor`, copied so the oracle shares none of
/// the crate's layout code: every row is scanned, a row naming no closure type
/// refuses when reached, and so does a second row for the queried type.
pub fn closure_layout_descriptor<'m>(
    m: &'m Module,
    closure: ClosureTyId,
) -> Result<Option<&'m trust_ir::ClosureLayoutDescriptor>, LayoutError> {
    let mut found = None;
    for desc in &m.closure_layouts {
        if m.closure_type(desc.closure).is_none() {
            return Err(LayoutError::ClosureLayoutIncoherent(desc.closure));
        }
        if desc.closure == closure {
            if found.is_some() {
                return Err(LayoutError::ClosureLayoutIncoherent(desc.closure));
            }
            found = Some(desc);
        }
    }
    Ok(found)
}

// ---------------------------------------------------------------------------
// Inhabitedness: the least fixpoint, stated naively
// ---------------------------------------------------------------------------

/// A node of the inhabitedness rules.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum INode {
    Entry(usize),
    Struct(StructId),
    Record(RecordId),
    Enum(EnumId),
}

/// The least solution of the inhabitedness rules over every node of `m`:
/// start from "nothing is uninhabited" and apply the rules to every node
/// until nothing changes (each round adds a node, so at most one round per
/// node). Quadratic and obviously the definition.
pub struct LeastFixpoint<'m> {
    m: &'m Module,
    uninhabited: BTreeMap<INode, bool>,
}

fn source_references_exist<'a>(m: &'a Module, fields: impl Iterator<Item = &'a Ty>) -> bool {
    let mut pending: Vec<&Ty> = fields.collect();
    let mut visited = std::collections::BTreeSet::new();
    while let Some(ty) = pending.pop() {
        match ty {
            Ty::FnItem(id) => {
                let mut matching = m.functions.iter().filter(|function| function.id == *id);
                let Some(function) = matching.next() else {
                    return false;
                };
                if matching.next().is_some() || m.func_types.get(function.ty.as_usize()).is_none() {
                    return false;
                }
            }
            Ty::Array(id, _)
            | Ty::Set(id, _)
            | Ty::Sequence(id)
            | Ty::Refine(id, _)
            | Ty::FatPtr(trust_ir::ty::FatPtrKind::Slice(id)) => {
                let Some(base) = m.types.get(id.as_usize()) else {
                    return false;
                };
                if visited.insert((0u8, id.as_usize())) {
                    pending.push(base);
                }
            }
            Ty::Struct(id) => {
                let Some(def) = m.structs.iter().find(|d| d.id == *id) else {
                    return false;
                };
                if visited.insert((1, id.as_usize())) {
                    pending.extend(def.fields.iter().map(|f| &f.ty));
                }
            }
            Ty::Enum(id) => {
                let Some(def) = m.enums.iter().find(|d| d.id == *id) else {
                    return false;
                };
                if visited.insert((2, id.as_usize())) {
                    pending.extend(def.variants.iter().flat_map(|v| &v.fields));
                }
            }
            Ty::Record(id) => {
                let Some(def) = m.records.iter().find(|d| d.id == *id) else {
                    return false;
                };
                if visited.insert((3, id.as_usize())) {
                    pending.extend(def.fields.iter().map(|f| &f.ty));
                }
            }
            Ty::Closure(id) => {
                let Some(def) = m.closure_types.get(id.as_usize()) else {
                    return false;
                };
                if visited.insert((4, id.as_usize())) {
                    pending.extend(&def.captures);
                }
            }
            Ty::Tuple(items) => pending.extend(items),
            Ty::Vector(elem, _)
            | Ty::Ref(elem)
            | Ty::RefMut(elem)
            | Ty::PtrConst(elem)
            | Ty::PtrMut(elem)
            | Ty::Rc(elem) => pending.push(elem),
            Ty::Error => return false,
            _ => {}
        }
    }
    true
}

pub fn least_fixpoint(m: &Module) -> LeastFixpoint<'_> {
    let mut nodes: Vec<INode> = (0..m.types.len()).map(INode::Entry).collect();
    nodes.extend(m.structs.iter().map(|def| INode::Struct(def.id)));
    nodes.extend(m.records.iter().map(|def| INode::Record(def.id)));
    nodes.extend(m.enums.iter().map(|def| INode::Enum(def.id)));
    nodes.sort();
    nodes.dedup();
    let mut fixpoint = LeastFixpoint {
        m,
        uninhabited: nodes.iter().map(|node| (*node, false)).collect(),
    };
    loop {
        let mut changed = false;
        for &node in &nodes {
            if !fixpoint.uninhabited[&node] && fixpoint.rule(node) {
                fixpoint.uninhabited.insert(node, true);
                changed = true;
            }
        }
        if !changed {
            return fixpoint;
        }
    }
}

impl LeastFixpoint<'_> {
    fn node(&self, node: INode) -> bool {
        self.uninhabited.get(&node).copied().unwrap_or(false)
    }

    /// One application of the rules to `node`, reading the current verdicts.
    fn rule(&self, node: INode) -> bool {
        let m = self.m;
        match node {
            INode::Entry(index) => self.ty_is_uninhabited(&m.types[index]),
            INode::Struct(id) => {
                let defs: Vec<_> = m.structs.iter().filter(|def| def.id == id).collect();
                !defs.is_empty()
                    && defs.iter().all(|def| {
                        def.fields
                            .iter()
                            .any(|field| self.ty_is_uninhabited(&field.ty))
                    })
            }
            INode::Record(id) => {
                let defs: Vec<_> = m.records.iter().filter(|def| def.id == id).collect();
                !defs.is_empty()
                    && defs.iter().all(|def| {
                        def.fields
                            .iter()
                            .any(|field| self.ty_is_uninhabited(&field.ty))
                    })
            }
            INode::Enum(id) => {
                let defs: Vec<_> = m.enums.iter().filter(|def| def.id == id).collect();
                !defs.is_empty()
                    && defs.iter().all(|def| {
                        def.variants
                            .iter()
                            .all(|variant| self.variant_is_uninhabited(variant))
                    })
            }
        }
    }

    /// Is `ty` uninhabited under the current verdicts?
    pub fn ty_is_uninhabited(&self, ty: &Ty) -> bool {
        let m = self.m;
        match ty {
            Ty::Never => true,
            Ty::Tuple(elems) => elems.iter().any(|elem| self.ty_is_uninhabited(elem)),
            Ty::Array(elem, len) => {
                *len > 0 && m.ty(*elem).is_some() && self.node(INode::Entry(elem.as_usize()))
            }
            Ty::Refine(base, _) => {
                m.ty(*base).is_some() && self.node(INode::Entry(base.as_usize()))
            }
            Ty::Struct(id) => self.node(INode::Struct(*id)),
            Ty::Record(id) => self.node(INode::Record(*id)),
            Ty::Enum(id) => self.node(INode::Enum(*id)),
            _ => false,
        }
    }

    pub fn variant_is_uninhabited(&self, variant: &EnumVariant) -> bool {
        variant
            .fields
            .iter()
            .any(|field| self.ty_is_uninhabited(field))
    }
}

/// The niche-coverage rule over [`least_fixpoint`].
pub fn niche_unencoded_inhabited_variant(
    m: &Module,
    def: &EnumDef,
    untagged_variant: u32,
    niche_variants_start: u32,
    niche_variants_end: u32,
) -> Option<usize> {
    let fixpoint = least_fixpoint(m);
    def.variants
        .iter()
        .enumerate()
        .find(|(index, variant)| {
            let encoded = u32::try_from(*index).is_ok_and(|index| {
                index == untagged_variant
                    || (niche_variants_start..=niche_variants_end).contains(&index)
            });
            !encoded && !fixpoint.variant_is_uninhabited(variant)
        })
        .map(|(index, _)| index)
}

// ---------------------------------------------------------------------------
// Inhabitedness: the recursion the memo replaced, verbatim (8d3895d8)
// ---------------------------------------------------------------------------

pub fn old_ty_is_uninhabited(m: &Module, ty: &Ty) -> bool {
    old_ty_is_uninhabited_inner(m, ty, &mut UninhabitedGuard::default())
}

pub fn old_variant_is_uninhabited(m: &Module, variant: &EnumVariant) -> bool {
    let mut guard = UninhabitedGuard::default();
    variant
        .fields
        .iter()
        .any(|field| old_ty_is_uninhabited_inner(m, field, &mut guard))
}

fn old_ty_is_uninhabited_inner(m: &Module, ty: &Ty, guard: &mut UninhabitedGuard) -> bool {
    match ty {
        Ty::Never => true,
        Ty::Tuple(elems) => elems
            .iter()
            .any(|elem| old_ty_is_uninhabited_inner(m, elem, guard)),
        Ty::Array(elem, len) => {
            *len > 0
                && guard.memoized(UninhabitedNode::Ty(elem.as_usize()), |guard| {
                    m.ty(*elem)
                        .is_some_and(|elem| old_ty_is_uninhabited_inner(m, elem, guard))
                })
        }
        Ty::Refine(base, _) => guard.memoized(UninhabitedNode::Ty(base.as_usize()), |guard| {
            m.ty(*base)
                .is_some_and(|base| old_ty_is_uninhabited_inner(m, base, guard))
        }),
        Ty::Struct(id) => guard.memoized(UninhabitedNode::Struct(id.index()), |guard| {
            let mut defs = m.structs.iter().filter(|def| def.id == *id).peekable();
            defs.peek().is_some()
                && defs.all(|def| {
                    def.fields
                        .iter()
                        .any(|field| old_ty_is_uninhabited_inner(m, &field.ty, guard))
                })
        }),
        Ty::Record(id) => guard.memoized(UninhabitedNode::Record(id.index()), |guard| {
            let mut defs = m.records.iter().filter(|def| def.id == *id).peekable();
            defs.peek().is_some()
                && defs.all(|def| {
                    def.fields
                        .iter()
                        .any(|field| old_ty_is_uninhabited_inner(m, &field.ty, guard))
                })
        }),
        Ty::Enum(id) => guard.memoized(UninhabitedNode::Enum(id.index()), |guard| {
            let mut defs = m.enums.iter().filter(|def| def.id == *id).peekable();
            defs.peek().is_some()
                && defs.all(|def| {
                    def.variants.iter().all(|variant| {
                        variant
                            .fields
                            .iter()
                            .any(|field| old_ty_is_uninhabited_inner(m, field, guard))
                    })
                })
        }),
        _ => false,
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum UninhabitedNode {
    Ty(usize),
    Struct(u32),
    Record(u32),
    Enum(u32),
}

#[derive(Default)]
struct UninhabitedGuard {
    in_progress: std::collections::BTreeSet<UninhabitedNode>,
    decided: std::collections::BTreeMap<UninhabitedNode, bool>,
}

impl UninhabitedGuard {
    fn memoized(&mut self, node: UninhabitedNode, expand: impl FnOnce(&mut Self) -> bool) -> bool {
        if let Some(verdict) = self.decided.get(&node) {
            return *verdict;
        }
        if !self.in_progress.insert(node) {
            return false;
        }
        let verdict = expand(self);
        self.in_progress.remove(&node);
        self.decided.insert(node, verdict);
        verdict
    }
}
