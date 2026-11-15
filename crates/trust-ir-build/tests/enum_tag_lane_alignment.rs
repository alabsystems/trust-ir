// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS2.22 (F-056(b), review half): an enum tag lane's SIZE and its ALIGNMENT
//! are two different facts, and only the first is target-free.
//!
//! A declared `EnumLayoutDescriptor` places a lane — a `Direct` tag or a
//! `Niche` lane — at a byte offset, and three engines judge that placement:
//! the validator, the layout authority (`shape`), and the reference
//! interpreter. Until this increment the first two derived the lane's
//! ALIGNMENT from its byte COUNT (`tag_offset % tag_size`,
//! `tag_size > layout.align`), while the interpreter ASKED for it
//! (`byte_align_in`). Reusing the size is a guess: the i386 System V ABI
//! aligns `i64` to 4, and rustc aligns `i128` to 16 on x86_64/aarch64 while
//! other data layouts use 8 — which is why the 128-bit tag reprs cannot be
//! added (their wire batch is WS3.14(b), at its reserved version) until the
//! alignment comes from the target.
//!
//! It now does: `Module::enum_tag_repr_align` asks the layout authority, and a
//! target with no scalar table draws
//! `ValidationError::EnumTagTargetScalarLayoutUnavailable` — the enum sibling
//! of the struct rule's `TargetScalarLayoutUnavailable` — instead of a verdict
//! measured against the byte count. On every target TrustIR does have a table
//! for, every repr spellable today is naturally aligned, so no accepted module
//! changes verdict.

use trust_ir::shape::LayoutError;
use trust_ir::ty::{
    EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant, FieldDef, StructDef,
    StructRepr,
};
use trust_ir::value::{EnumId, StructId};
use trust_ir::{Endianness, Module, StructPassingPolicy, TargetInfo, Ty};
use trust_ir_build::validate::ValidationError;
use trust_ir_build::validate_module;

const E: EnumId = EnumId::new(0);
const I686: &str = "i686-unknown-linux-gnu";

fn variant(name: &str) -> EnumVariant {
    EnumVariant {
        name: name.into(),
        fields: Vec::new(),
        field_names: Vec::new(),
    }
}

/// A fieldless two-variant enum with an explicit tag repr and a `Direct`
/// descriptor placing the tag at `tag_offset` in a `size`/`align` image.
///
/// Fieldless on purpose: a payload field would make `shape` query the scalar
/// table for the FIELD and fail there, hiding whether the TAG's alignment was
/// asked for at all.
fn direct(repr: EnumTagRepr, tag_offset: u64, size: u64, align: u64) -> EnumDef {
    let mut def = EnumDef::new(E, "E", vec![variant("A"), variant("B")]);
    def.repr = Some(repr);
    def.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Direct { tag_offset },
        size,
        align,
        variant_field_offsets: vec![vec![], vec![]],
    });
    def
}

/// The same image with a `Niche` lane instead of a direct tag: `A` untagged,
/// carrying one field of the lane's own type at `niche_offset` (the niche
/// rule requires a non-ZST field of the untagged variant to cover the lane),
/// `B` the single niche variant.
fn niche(lane: EnumTagRepr, niche_offset: u64, size: u64, align: u64) -> EnumDef {
    let untagged = EnumVariant {
        name: "A".into(),
        fields: vec![lane.ty()],
        field_names: Vec::new(),
    };
    let mut def = EnumDef::new(E, "E", vec![untagged, variant("B")]);
    def.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Niche {
            untagged_variant: 0,
            niche_variants_start: 1,
            niche_variants_end: 1,
            niche_start: 1,
            niche_offset,
            niche_ty: lane,
        },
        size,
        align,
        variant_field_offsets: vec![vec![niche_offset], vec![]],
    });
    def
}

fn module_with(def: EnumDef) -> Module {
    let mut module = Module::new("enum_tag_lane_alignment");
    module.add_enum(def);
    module
}

fn on_target(mut module: Module, triple: &str, pointer_size: u32) -> Module {
    module.target_info = Some(TargetInfo {
        triple: triple.into(),
        pointer_size,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    });
    module
}

fn x86_64(module: Module) -> Module {
    on_target(module, "x86_64-unknown-linux-gnu", 8)
}

fn shape_of(module: &Module) -> Result<u64, LayoutError> {
    module
        .ty_layout_shape(&Ty::Enum(E))
        .map(|layout| layout.size_bits)
}

// ─────────────────────────── the size/align split ───────────────────────────

/// A tag repr's SIZE is a property of the repr alone: the width of its integer
/// type, the same number on every target, and the exhaustive destructure keeps
/// it that way when a repr is added.
#[test]
fn tag_repr_size_is_the_integer_width_on_every_target() {
    for (repr, bytes) in [
        (EnumTagRepr::U8, 1),
        (EnumTagRepr::U16, 2),
        (EnumTagRepr::U32, 4),
        (EnumTagRepr::U64, 8),
        (EnumTagRepr::I8, 1),
        (EnumTagRepr::I16, 2),
        (EnumTagRepr::I32, 4),
        (EnumTagRepr::I64, 8),
    ] {
        assert_eq!(repr.size_bytes(), bytes, "{repr}");
        // The size is the type's own width, whatever the target says.
        for module in [
            Module::new("target-free"),
            x86_64(Module::new("x86_64")),
            on_target(Module::new("i686"), I686, 4),
        ] {
            let _ = module;
            assert_eq!(repr.size_bytes(), bytes, "{repr}");
        }
    }
}

/// A tag repr's ALIGNMENT is asked of the layout authority, and on a target
/// TrustIR has a scalar table for it is the natural alignment — the SAME
/// number the reference interpreter's `byte_align_in` reports, which is what
/// lets the three engines agree on a descriptor's verdict.
#[test]
fn tag_repr_align_comes_from_the_layout_authority() {
    let module = x86_64(Module::new("x86_64"));
    for (repr, align) in [
        (EnumTagRepr::U8, 1),
        (EnumTagRepr::U16, 2),
        (EnumTagRepr::U32, 4),
        (EnumTagRepr::U64, 8),
        (EnumTagRepr::I8, 1),
        (EnumTagRepr::I16, 2),
        (EnumTagRepr::I32, 4),
        (EnumTagRepr::I64, 8),
    ] {
        assert_eq!(module.enum_tag_repr_align(repr), Ok(align), "{repr}");
        assert_eq!(
            Module::new("target-free").enum_tag_repr_align(repr),
            Ok(align),
            "{repr} target-free"
        );
    }
}

/// The query FAILS on a target with no scalar table rather than answering with
/// the byte count. This is the fact the descriptor rules below rest on.
#[test]
fn tag_repr_align_fails_closed_off_the_canonical_scalar_table() {
    let module = on_target(Module::new("i686"), I686, 4);
    assert!(!module.target_has_canonical_scalar_layout());
    assert_eq!(
        module.enum_tag_repr_align(EnumTagRepr::U64),
        Err(LayoutError::TargetScalarLayoutUnavailable {
            triple: I686.into()
        })
    );
}

// ───────────────────────── positive fixture (canonical) ─────────────────────

/// Positive: a `u32` tag at offset 4 in an align-4 image validates and lays
/// out, on the pinned canonical target and target-free alike. Its verdict is
/// unchanged by this increment — every repr spellable today is naturally
/// aligned on every target TrustIR tabulates, so asking instead of guessing
/// moves no accepted module.
#[test]
fn a_naturally_aligned_lane_validates_on_a_canonical_target() {
    for module in [
        module_with(direct(EnumTagRepr::U32, 4, 8, 4)),
        x86_64(module_with(direct(EnumTagRepr::U32, 4, 8, 4))),
        on_target(module_with(direct(EnumTagRepr::U32, 4, 8, 4)), "wasm32", 4),
    ] {
        assert_eq!(validate_module(&module), vec![], "{}", module.name);
        assert_eq!(shape_of(&module), Ok(64), "{}", module.name);
    }
    let niched = x86_64(module_with(niche(EnumTagRepr::U32, 4, 8, 4)));
    assert_eq!(validate_module(&niched), vec![]);
    assert_eq!(shape_of(&niched), Ok(64));
}

// ───────────── negative twin: the specific named refusal, by target ─────────

/// Negative twin: the SAME well-formed descriptor on i686 — a target whose
/// scalar ABI TrustIR does not tabulate — is refused by name. The old rule
/// accepted it, having read the alignment off the byte count; an unknown ABI
/// is not evidence that `tag_offset 4` is aligned for a `u32`.
#[test]
fn an_unknown_target_refuses_the_direct_tag_by_name() {
    let module = on_target(module_with(direct(EnumTagRepr::U32, 4, 8, 4)), I686, 4);
    assert_eq!(
        validate_module(&module),
        vec![ValidationError::EnumTagTargetScalarLayoutUnavailable {
            enum_id: 0,
            triple: I686.into(),
        }]
    );
    assert_eq!(
        shape_of(&module),
        Err(LayoutError::TargetScalarLayoutUnavailable {
            triple: I686.into()
        })
    );
    assert!(
        validate_module(&module)[0]
            .to_string()
            .contains("tag lane's alignment cannot be judged"),
        "{}",
        validate_module(&module)[0]
    );
}

/// The niche lane is the same rule through the same helper: it is refused by
/// the same name on the same target. (The untagged variant's covering field
/// has no resolvable layout on i686 either, and that draws its own field
/// error beside the lane's; the lane's refusal is the one this test is
/// about, and it is present exactly once.)
#[test]
fn an_unknown_target_refuses_the_niche_lane_by_name() {
    let module = on_target(module_with(niche(EnumTagRepr::U32, 4, 8, 4)), I686, 4);
    let errors = validate_module(&module);
    assert_eq!(
        errors
            .iter()
            .filter(|e| matches!(
                e,
                ValidationError::EnumTagTargetScalarLayoutUnavailable { enum_id: 0, triple }
                    if triple == I686
            ))
            .count(),
        1,
        "{errors:#?}"
    );
    assert_eq!(
        shape_of(&module),
        Err(LayoutError::TargetScalarLayoutUnavailable {
            triple: I686.into()
        })
    );
}

/// The refusal is about the TARGET, not about the offset: a lane at offset 0,
/// which no alignment rule could ever reject, is refused just the same. This
/// is the half the old code silently blessed — it "checked" `0 % 8 == 0` and
/// called the descriptor judged.
#[test]
fn an_unknown_target_refuses_even_a_trivially_aligned_lane() {
    let module = on_target(module_with(direct(EnumTagRepr::U64, 0, 8, 8)), I686, 4);
    assert_eq!(
        validate_module(&module),
        vec![ValidationError::EnumTagTargetScalarLayoutUnavailable {
            enum_id: 0,
            triple: I686.into(),
        }]
    );
}

/// An `Untagged` descriptor has no lane at all, so it asks the authority
/// nothing and is judged on every target — the refusal is scoped to a lane
/// that actually exists.
#[test]
fn an_untagged_descriptor_needs_no_lane_alignment() {
    let mut def = EnumDef::new(E, "E", vec![variant("A")]);
    def.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Untagged,
        size: 0,
        align: 1,
        variant_field_offsets: vec![vec![]],
    });
    let module = on_target(module_with(def), I686, 4);
    assert_eq!(validate_module(&module), vec![]);
}

/// Review: the architecture spelling is not the table. An `x86_64` triple with
/// 32-bit pointers is a forged canonical target (the struct rule's
/// `target_pinned_layout_declines_a_forged_canonical_triple_width`), and the
/// tag lane's alignment is refused for it by the same name — the triple in the
/// error is the forged one, so the refusal names what it judged.
#[test]
fn a_forged_canonical_triple_refuses_the_lane_by_name() {
    const FORGED: &str = "x86_64-unknown-linux-gnu";
    let module = on_target(module_with(direct(EnumTagRepr::U32, 4, 8, 4)), FORGED, 4);
    assert!(!module.target_has_canonical_scalar_layout());
    assert_eq!(
        validate_module(&module),
        vec![ValidationError::EnumTagTargetScalarLayoutUnavailable {
            enum_id: 0,
            triple: FORGED.into(),
        }]
    );
    assert_eq!(
        shape_of(&module),
        Err(LayoutError::TargetScalarLayoutUnavailable {
            triple: FORGED.into()
        })
    );
}

// ───────────── review: the descriptor-LESS canonical layout asks too ─────────

/// Review (found while breaking the increment): the layout authority's
/// CANONICAL enum layout — the one an enum without a descriptor gets — set the
/// enum's alignment to `max(tag SIZE, payload align)`, the same byte-count
/// guess the descriptor clauses had made, while the interpreter's canonical
/// layout takes `max(tag ALIGN, payload align)` with the alignment asked of
/// `byte_align_in`. So a fieldless enum with no descriptor on i686 — which has
/// no field to draw the scalar-table refusal — laid out with an alignment read
/// off its tag's width. It now asks, and is refused on the target the table
/// does not cover; a target it does cover is unchanged.
#[test]
fn a_descriptor_less_enum_asks_the_target_for_its_tag_alignment() {
    let fieldless = |repr: EnumTagRepr| {
        let mut def = EnumDef::new(E, "E", vec![variant("A"), variant("B")]);
        def.repr = Some(repr);
        def
    };
    for module in [
        module_with(fieldless(EnumTagRepr::U64)),
        x86_64(module_with(fieldless(EnumTagRepr::U64))),
        on_target(module_with(fieldless(EnumTagRepr::U64)), "wasm32", 4),
    ] {
        let layout = module
            .ty_layout_shape(&Ty::Enum(E))
            .unwrap_or_else(|e| panic!("{}: {e}", module.name));
        assert_eq!((layout.size_bits, layout.align_bits), (64, Some(64)));
    }
    let i686 = on_target(module_with(fieldless(EnumTagRepr::U64)), I686, 4);
    assert_eq!(
        shape_of(&i686),
        Err(LayoutError::TargetScalarLayoutUnavailable {
            triple: I686.into()
        })
    );
}

/// The same guess, seen from the validator: a declared struct layout whose
/// field is that fieldless enum. The struct rule asks the layout authority for
/// each field's alignment and refuses an unknown target by name
/// (`TargetScalarLayoutUnavailable`) — but for an ENUM field the authority
/// used to answer from the tag's byte count, so the struct validated on i686.
/// It is now refused, exactly as the same struct with a `u64` field is.
#[test]
fn a_struct_holding_a_fieldless_enum_is_refused_on_an_unknown_target() {
    let struct_with = |field_ty: Ty| {
        let mut def = EnumDef::new(E, "E", vec![variant("A"), variant("B")]);
        def.repr = Some(EnumTagRepr::U64);
        let mut module = module_with(def);
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "S".into(),
            fields: vec![FieldDef {
                name: "f".into(),
                ty: field_ty,
                offset: Some(0),
            }],
            size: Some(8),
            align: Some(8),
            repr: StructRepr::C,
            origin: None,
        });
        module
    };
    assert_eq!(validate_module(&x86_64(struct_with(Ty::Enum(E)))), vec![]);
    let control = on_target(struct_with(Ty::U64), I686, 4);
    assert_eq!(
        validate_module(&control),
        vec![ValidationError::TargetScalarLayoutUnavailable {
            struct_id: 0,
            triple: I686.into(),
        }]
    );
    let refused = on_target(struct_with(Ty::Enum(E)), I686, 4);
    assert_eq!(validate_module(&refused), validate_module(&control));
}

/// Mutation control for the canonical layout: its alignment is
/// `max(tag align, payload align)`, with the tag's alignment the one the
/// authority reports for the tag type — so an `i64`-tagged enum with a `u8`
/// payload is align 8 (the tag wins) and a `u8`-tagged enum with a `u64`
/// payload is align 8 (the payload wins), on the pinned canonical target and
/// target-free alike. A rule that had dropped the tag from the max, or wired
/// it to a constant, fails on one of the two.
#[test]
fn the_canonical_alignment_is_the_max_of_tag_and_payload_alignment() {
    let tagged = |repr: EnumTagRepr, payload: Ty| {
        let mut def = EnumDef::new(
            E,
            "E",
            vec![
                variant("A"),
                EnumVariant {
                    name: "B".into(),
                    fields: vec![payload],
                    field_names: Vec::new(),
                },
            ],
        );
        def.repr = Some(repr);
        def
    };
    for (module, size_bits) in [
        (module_with(tagged(EnumTagRepr::I64, Ty::U8)), 128),
        (x86_64(module_with(tagged(EnumTagRepr::I64, Ty::U8))), 128),
        (module_with(tagged(EnumTagRepr::U8, Ty::U64)), 128),
        (x86_64(module_with(tagged(EnumTagRepr::U8, Ty::U64))), 128),
        (x86_64(module_with(tagged(EnumTagRepr::U8, Ty::U16))), 32),
    ] {
        let layout = module
            .ty_layout_shape(&Ty::Enum(E))
            .unwrap_or_else(|e| panic!("{}: {e}", module.name));
        assert_eq!(
            (layout.size_bits, layout.align_bits),
            (size_bits, Some(if size_bits == 32 { 16 } else { 64 })),
            "{}",
            module.name
        );
    }
}

// ───────────── review: the ask is scoped to the lane that EXISTS ────────────

/// Review: the two engines a validated module is judged by must draw the SAME
/// line on a target off the scalar table. An `Untagged` descriptor stores no
/// lane, so the validator asks nothing and accepts it — and `shape` must lay
/// it out too (at the descriptor's own size and align), or the struct rule,
/// which asks the layout authority for each field, refuses a struct holding
/// the enum that the enum rule just accepted. Before this pin, the canonical
/// tag's alignment was asked for unconditionally and the layout of a tag-FREE
/// image failed on the alignment of a tag it does not store.
#[test]
fn an_untagged_descriptor_lays_out_where_the_validator_accepts_it() {
    let untagged = || {
        let mut def = EnumDef::new(E, "E", vec![variant("A")]);
        def.layout = Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Untagged,
            size: 0,
            align: 1,
            variant_field_offsets: vec![vec![]],
        });
        def
    };
    for module in [
        on_target(module_with(untagged()), I686, 4),
        x86_64(module_with(untagged())),
    ] {
        assert_eq!(validate_module(&module), vec![], "{}", module.name);
        let layout = module
            .ty_layout_shape(&Ty::Enum(E))
            .unwrap_or_else(|e| panic!("{}: {e}", module.name));
        assert_eq!((layout.size_bits, layout.align_bits), (0, Some(8)));
    }
    // A declared struct holding the tag-free enum: the struct rule asks the
    // layout authority for the field, and the TARGET adds nothing to its
    // verdict — i686 and x86_64 draw the same error list, and neither is a
    // scalar-table refusal. (The list is not empty: the struct rule's ZST
    // predicate does not prove an ENUM zero-sized on any target, a
    // pre-existing conservatism this pin is not about.)
    let holder = |module: Module| {
        let mut module = module;
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "S".into(),
            fields: vec![FieldDef {
                name: "f".into(),
                ty: Ty::Enum(E),
                offset: Some(0),
            }],
            size: Some(0),
            align: Some(1),
            repr: StructRepr::C,
            origin: None,
        });
        module
    };
    let off_table = validate_module(&holder(on_target(module_with(untagged()), I686, 4)));
    let on_table = validate_module(&holder(x86_64(module_with(untagged()))));
    assert_eq!(off_table, on_table);
    assert!(
        !off_table.iter().any(|e| matches!(
            e,
            ValidationError::TargetScalarLayoutUnavailable { .. }
                | ValidationError::EnumTagTargetScalarLayoutUnavailable { .. }
        )),
        "{off_table:#?}"
    );
}

/// Review: a `Direct` descriptor on an enum with NO canonical tag (a `u8`
/// hint the discriminant 300 does not fit) has no lane type to ask the target
/// about. It is refused for the missing tag — the cause — and draws no
/// target refusal beside it, on and off the scalar table alike: the lane
/// refusal names a lane that exists.
#[test]
fn a_direct_descriptor_without_a_canonical_tag_draws_no_lane_refusal() {
    let tagless = || {
        let mut def = direct(EnumTagRepr::U8, 0, 1, 1);
        def.discriminants = vec![Some(0), Some(300)];
        assert_eq!(def.canonical_tag_repr(), None);
        def
    };
    for module in [
        on_target(module_with(tagless()), I686, 4),
        x86_64(module_with(tagless())),
    ] {
        let errors = validate_module(&module);
        assert!(
            errors
                .iter()
                .any(|e| e.to_string().contains("no canonical tag")),
            "{}: {errors:#?}",
            module.name
        );
        assert!(
            !errors.iter().any(|e| matches!(
                e,
                ValidationError::EnumTagTargetScalarLayoutUnavailable { .. }
            )),
            "{}: {errors:#?}",
            module.name
        );
        assert_eq!(
            shape_of(&module),
            Err(LayoutError::EnumLayoutUnavailable(E))
        );
    }
}

/// Review: the target table the lane rule consults is the struct rule's, not
/// a second one — `riscv64` and `aarch64` are tabulated (pointer width 8),
/// `riscv32` is not, and a big-endian `aarch64_be` spelling is not.
#[test]
fn the_lane_rule_consults_the_struct_rules_target_table() {
    for (triple, pointer_size) in [
        ("riscv64gc-unknown-linux-gnu", 8),
        ("aarch64-apple-darwin", 8),
        ("wasm64-unknown-unknown", 8),
    ] {
        let module = on_target(
            module_with(direct(EnumTagRepr::U64, 0, 8, 8)),
            triple,
            pointer_size,
        );
        assert!(module.target_has_canonical_scalar_layout(), "{triple}");
        assert_eq!(validate_module(&module), vec![], "{triple}");
        assert_eq!(shape_of(&module), Ok(64), "{triple}");
    }
    for (triple, pointer_size) in [
        ("riscv32imac-unknown-none-elf", 4),
        ("aarch64_be-unknown-linux-gnu", 8),
        ("avr-unknown-gnu-atmega328", 2),
    ] {
        let module = on_target(
            module_with(direct(EnumTagRepr::U64, 0, 8, 8)),
            triple,
            pointer_size,
        );
        assert!(!module.target_has_canonical_scalar_layout(), "{triple}");
        assert_eq!(
            validate_module(&module),
            vec![ValidationError::EnumTagTargetScalarLayoutUnavailable {
                enum_id: 0,
                triple: triple.into(),
            }],
            "{triple}"
        );
        assert_eq!(
            shape_of(&module),
            Err(LayoutError::TargetScalarLayoutUnavailable {
                triple: triple.into()
            }),
            "{triple}"
        );
    }
}

// ──────────────────────────── mutation controls ─────────────────────────────

/// Mutation control, niche over-alignment half: a niche lane may not out-align
/// the image that holds it, and the number the rule uses is the LANE's
/// alignment. A `u32` lane at offset 0 in an align-2 image is refused by the
/// containing-align clause — separately from the placement clause, which
/// `0 % 4 == 0` satisfies — and `shape` refuses the same descriptor.
#[test]
fn a_niche_lane_may_not_out_align_its_image() {
    let module = x86_64(module_with(niche(EnumTagRepr::U32, 0, 4, 2)));
    let errors: Vec<String> = validate_module(&module)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert!(
        errors
            .iter()
            .any(|e| e.contains("descriptor align at least niche alignment 4")),
        "{errors:#?}"
    );
    assert!(
        !errors.iter().any(|e| e.contains("a niche lane aligned to")),
        "{errors:#?}"
    );
    assert_eq!(
        shape_of(&module),
        Err(LayoutError::EnumLayoutUnavailable(E))
    );
}

/// Mutation control: the alignment tracks the LANE TYPE. At the same offset 4
/// in the same image, a `u32` lane is accepted and a `u64` lane is refused as
/// misaligned — so a rule that had been frozen to one constant, or wired to
/// the descriptor's own `align`, fails here.
#[test]
fn the_alignment_tracks_the_lane_type_not_the_descriptor() {
    let accepted = x86_64(module_with(direct(EnumTagRepr::U32, 4, 8, 4)));
    assert_eq!(validate_module(&accepted), vec![]);

    let refused = x86_64(module_with(direct(EnumTagRepr::U64, 4, 16, 8)));
    let errors: Vec<String> = validate_module(&refused)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert_eq!(errors.len(), 1, "{errors:#?}");
    assert!(
        errors[0].contains("a direct tag aligned to 8 bytes"),
        "{}",
        errors[0]
    );
    assert_eq!(
        shape_of(&refused),
        Err(LayoutError::EnumLayoutUnavailable(E))
    );
}

/// Mutation control, over-alignment half: a lane may not out-align the image
/// that contains it, and the number the rule uses is the lane's alignment. An
/// `i64` lane in an align-4 image is refused on both sides — the placement
/// rule and the containing-align rule — and the SIZE clause stays separate:
/// the lane still has to fit.
#[test]
fn a_lane_may_not_out_align_or_overrun_its_image() {
    let module = x86_64(module_with(direct(EnumTagRepr::I64, 4, 8, 4)));
    let errors: Vec<String> = validate_module(&module)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert!(
        errors
            .iter()
            .any(|e| e.contains("a direct tag aligned to 8 bytes")),
        "{errors:#?}"
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("descriptor align at least direct-tag alignment 8")),
        "{errors:#?}"
    );
    assert!(
        errors
            .iter()
            .any(|e| e.contains("a direct tag (8 bytes) within size 8")),
        "{errors:#?}"
    );
}

/// Mutation control for the niche half: same offset, two lane widths, two
/// verdicts.
#[test]
fn the_niche_lane_alignment_tracks_the_lane_type() {
    let accepted = x86_64(module_with(niche(EnumTagRepr::U16, 2, 8, 2)));
    assert_eq!(validate_module(&accepted), vec![]);

    let refused = x86_64(module_with(niche(EnumTagRepr::U32, 2, 8, 4)));
    let errors: Vec<String> = validate_module(&refused)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert!(
        errors
            .iter()
            .any(|e| e.contains("a niche lane aligned to 4 bytes")),
        "{errors:#?}"
    );
    assert_eq!(
        shape_of(&refused),
        Err(LayoutError::EnumLayoutUnavailable(E))
    );
}

// ──────────────────── the per-variant field-overlap rule ────────────────────

/// Every overlapping pair of a variant's sized fields is reported, in the
/// order a loop over `left` and then `right > left` would report it — now
/// found by a sweep, each field's size asked once — on a variant that mixes
/// disjoint, touching, nested, duplicate, zero-sized and unsized fields.
#[test]
fn every_overlapping_field_pair_is_reported_in_pair_order() {
    // (type, offset): u8 @0, a missing struct @0 (no size: skipped, and
    // every later index must still be the field's own), u16 @0 (overlaps 0),
    // u8 @2 (touches 2), u32 @0 (overlaps 0, 2, 3), () @1 (zero-sized:
    // never), u8 @2 (overlaps 3, 4), u16 @6 (disjoint).
    let fields = [
        (Ty::U8, 0),
        (Ty::Struct(StructId::new(9)), 0),
        (Ty::U16, 0),
        (Ty::U8, 2),
        (Ty::U32, 0),
        (Ty::Unit, 1),
        (Ty::U8, 2),
        (Ty::U16, 6),
    ];
    let untagged = EnumVariant {
        name: "A".into(),
        fields: fields.iter().map(|(ty, _)| ty.clone()).collect(),
        field_names: Vec::new(),
    };
    let mut def = EnumDef::new(E, "E", vec![untagged]);
    def.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Untagged,
        size: 8,
        align: 4,
        variant_field_offsets: vec![fields.iter().map(|(_, offset)| *offset).collect()],
    });
    let module = x86_64(module_with(def));
    let reported: Vec<String> = validate_module(&module)
        .iter()
        .map(ToString::to_string)
        .filter(|error| error.contains("occupy disjoint byte ranges"))
        .collect();
    let expected: Vec<String> = [(0, 2), (0, 4), (2, 4), (3, 4), (3, 6), (4, 6)]
        .iter()
        .map(|(left, right)| {
            format!(
                "fields {left} and {right} overlap at offsets {} and {}",
                fields[*left].1, fields[*right].1
            )
        })
        .collect();
    assert_eq!(reported.len(), expected.len(), "{reported:#?}");
    for (reported, expected) in reported.iter().zip(&expected) {
        assert!(reported.contains(expected), "{reported} vs {expected}");
    }
}

/// The niche rule exempts an uninhabited variant through the pass's one
/// layout table, also when the payload reaches its `!` through a chain of
/// structs (decided once, on the heap).
#[test]
fn the_niche_rule_exempts_a_variant_uninhabited_through_a_struct_chain() {
    let depth = 500u32;
    let mut module = x86_64(Module::new("niche_over_a_chain"));
    for i in 0..depth {
        let ty = if i + 1 < depth {
            Ty::Struct(StructId::new(i + 1))
        } else {
            Ty::Enum(EnumId::new(1))
        };
        module.add_struct(StructDef {
            id: StructId::new(i),
            name: format!("S{i}"),
            fields: vec![FieldDef {
                name: "f".into(),
                ty,
                // A zero-sized field needs no offset.
                offset: None,
            }],
            size: Some(0),
            align: Some(1),
            repr: StructRepr::C,
            origin: None,
        });
    }
    let mut def = EnumDef::new(
        E,
        "E",
        vec![
            EnumVariant {
                name: "A".into(),
                fields: vec![Ty::U8],
                field_names: Vec::new(),
            },
            EnumVariant {
                name: "B".into(),
                fields: vec![Ty::Struct(StructId::new(0))],
                field_names: Vec::new(),
            },
        ],
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
        size: 1,
        align: 1,
        variant_field_offsets: vec![vec![0], vec![0]],
    });
    module.add_enum(def);
    let mut void = EnumDef::new(
        EnumId::new(1),
        "Void",
        vec![EnumVariant {
            name: "V".into(),
            fields: vec![Ty::Never],
            field_names: Vec::new(),
        }],
    );
    void.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Untagged,
        size: 0,
        align: 1,
        variant_field_offsets: vec![vec![0]],
    });
    module.add_enum(void);
    assert_eq!(validate_module(&module), vec![]);
    assert_eq!(shape_of(&module), Ok(8));
    // The control: a `u8` at the chain's end makes `B` inhabited, so the
    // niche (which encodes only `A`) no longer covers it.
    module.structs[depth as usize - 1].fields[0].ty = Ty::U8;
    module.structs[depth as usize - 1].size = Some(1);
    let errors: Vec<String> = validate_module(&module)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert!(
        errors
            .iter()
            .any(|e| e.contains("inhabited variant 1 (B) is neither untagged 0")),
        "{errors:#?}"
    );
}
