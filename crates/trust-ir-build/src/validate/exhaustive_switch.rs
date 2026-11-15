// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS2.6 (F-039): `Switch.exhaustive_enum_unreachable` gets a validator reader.
//!
//! The flag is a PRODUCER-ASSERTED, ZERO-AUTHORITY hint (`inst.rs`). Until
//! this pass nothing read it, so a switch with a LIVE default arm, or one over
//! an enum whose case set omits an inhabited variant, could carry it and
//! validate for codegen — and a consumer that conjoined `selector ∈ {cases}`
//! into the default arm (the CHC translator does) made that live arm
//! vacuously provable. Two rules, each stating ONLY what it checks:
//!
//! 1. **The default edge is the dead arm the flag describes**
//!    ([`validate_exhaustive_switch_shape`], function-local, so
//!    `validate_function` and `validate_module` agree):
//!    * (i) `default_args` is empty;
//!    * (ii) the `default` block has no parameters and its body is exactly
//!      `[Unreachable]`;
//!    * (iii) the case values are distinct AS SELECTOR VALUES — two spellings
//!      of one value under the selector's width are one case, not two. The
//!      width is the reference interpreter's: an integer's own, the target
//!      pointer width for `isize`/`usize`, 32 for `char`. Since
//!      SPEC_RATIFICATIONS §3.3 every case at an integer or `char` selector
//!      is also range-checked at its type by the constant funnel
//!      (`ConstTypeMismatch`), which refuses `-1` at `u8`, `2^64` at `usize`
//!      and `2^32 + 65` at `char`; the alias this clause alone still sees is
//!      the funnel's 64-bit `usize` range on a narrower target (`0` and `2^32`
//!      at a 32-bit `usize`). A syntactically repeated constant is already
//!      `DuplicateSwitchCase` for every switch and is not reported twice.
//!
//!    Otherwise `ExhaustiveSwitchDefaultReachable`, the failing clause named in
//!    `reason`. A default target that does not exist is left to
//!    `BranchTargetNotFound`.
//! 2. **The case set covers the enum** ([`validate_exhaustive_switch_cases`],
//!    module-level, because it needs the enum definition). When the
//!    selector's definition — through `Copy` and value-preserving integer
//!    widenings (`zext`, `sext`, equal-width `bitcast`: the Trust bridge's
//!    `Rvalue::Discriminant` lowering widens the canonical tag to the MIR
//!    discriminant type with exactly one) — is `ExtractField { field: 0 }` of
//!    a `Ty::Enum` value in the same function, every case value must be the
//!    selector value of one of that enum's effective discriminants (each
//!    discriminant carried through the same casts), and every discriminant
//!    MISSING from the case set must belong to a variant the format proves
//!    uninhabited — [`Module::variant_is_uninhabited`], the one predicate
//!    that also refuses CONSTRUCTING such a variant
//!    (`UninhabitedVariantConstructed`) and decoding one in the interpreter:
//!    a by-value `Never` field, or an enum all of whose variants are
//!    uninhabited, reached through by-value struct / record / tuple /
//!    refinement / non-empty-array containment. Otherwise
//!    `ExhaustiveSwitchCasesIncomplete`. A rustc-vetted match may omit an
//!    uninhabited arm, so "case set == every discriminant" would refuse
//!    legitimate modules; anything the predicate cannot PROVE uninhabited is
//!    still refused, so the rule stays fail-closed.
//!
//! When the selector's provenance does not resolve (a block parameter, a call
//! result, a load of an integer, a narrowing cast), only rule 1 applies — the flag then claims
//! nothing the validator checked about the case set, and a verifier MUST NOT
//! use it as a fact without re-deriving that set (the `inst.rs` doc).
//!
//! When the provenance resolves to an enum whose discriminants or tag repr do
//! not resolve, rule 2 is skipped because the module is already refused
//! elsewhere (the enum def-level checks, and WS2.2's lane-0 typing refuses
//! every projection of an enum with no canonical tag repr).

use super::{ValidationError, build_function_value_types};
use std::collections::{BTreeMap, BTreeSet};
use trust_ir::ty::{EnumDef, Ty};
use trust_ir::value::ValueId;
use trust_ir::{CastOp, Constant, Function, Inst, Module};

/// The width at which a `Switch` selector of type `ty` compares its cases —
/// the reference interpreter's `int_shape` generalized to the target: a
/// fixed-width integer's own width, a pointer-width integer's `pointer_bits`
/// (the interpreter models 64, the default), and `char`'s 32-bit carrier.
/// `None` for every other type: then only syntactic equality
/// (`DuplicateSwitchCase`) speaks.
fn selector_width(ty: &Ty, pointer_bits: u32) -> Option<u32> {
    if ty.is_integer() || matches!(ty, Ty::Char) {
        ty.bit_width_with(pointer_bits)
    } else {
        None
    }
}

/// A case constant as a selector value: its two's-complement bits masked to
/// the selector's width `bits`, the exact equality the reference
/// interpreter's `Switch` decides (`constant_to_value` masks an `Int` into
/// the selector type). `None` when the constant is not an integer.
fn case_bits(bits: u32, value: &Constant) -> Option<u128> {
    let raw = match value {
        Constant::Int(v) => *v as u128,
        Constant::U128(v) => *v,
        _ => return None,
    };
    Some(mask(raw, bits))
}

fn mask(raw: u128, bits: u32) -> u128 {
    if bits >= 128 {
        raw
    } else {
        raw & ((1u128 << bits) - 1)
    }
}

/// Rule 1 (function-local): the default edge of a flagged `Switch` is the
/// dead arm the flag describes. See the module doc.
pub(super) fn validate_exhaustive_switch_shape(
    func: &Function,
    pointer_bits: u32,
) -> Vec<ValidationError> {
    let mut errors = Vec::new();
    let mut val_ty: Option<BTreeMap<u32, Ty>> = None;
    for block in &func.blocks {
        let Some(term) = block.terminator() else {
            continue;
        };
        let Inst::Switch {
            value,
            default,
            default_args,
            cases,
            exhaustive_enum_unreachable: true,
        } = &term.inst
        else {
            continue;
        };
        let block_id = block.id.index();
        let mut refuse = |reason: String| {
            errors.push(ValidationError::ExhaustiveSwitchDefaultReachable {
                block: block_id,
                reason,
            });
        };
        // (i) the default edge carries nothing.
        if !default_args.is_empty() {
            refuse(format!(
                "the default edge to bb{} passes {} argument(s); a dead default carries none",
                default.index(),
                default_args.len()
            ));
        }
        // (ii) the default block is exactly `[Unreachable]` with no parameters.
        if let Some(target) = func.blocks.iter().find(|b| b.id == *default) {
            if !target.params.is_empty() {
                refuse(format!(
                    "the default block bb{} has {} parameter(s); a dead default has none",
                    default.index(),
                    target.params.len()
                ));
            }
            let is_unreachable_only =
                matches!(target.body.as_slice(), [only] if matches!(only.inst, Inst::Unreachable));
            if !is_unreachable_only {
                refuse(format!(
                    "the default block bb{} is not exactly [unreachable] ({} instruction(s))",
                    default.index(),
                    target.body.len()
                ));
            }
        }
        // (iii) distinct as selector values. Syntactic repeats are
        // `DuplicateSwitchCase` already; only an ALIAS under the selector
        // width is reported here.
        let ty = val_ty
            .get_or_insert_with(|| build_function_value_types(func))
            .get(&value.index())
            .cloned();
        let width = ty.as_ref().and_then(|t| selector_width(t, pointer_bits));
        let mut seen: BTreeMap<u128, &Constant> = BTreeMap::new();
        for case in cases {
            let Some(bits) = width.and_then(|w| case_bits(w, &case.value)) else {
                continue;
            };
            match seen.get(&bits) {
                Some(first) if format!("{first}") != format!("{}", case.value) => {
                    refuse(format!(
                        "case values {first} and {} denote the same {} selector value",
                        case.value,
                        ty.as_ref().map_or_else(String::new, |t| format!("{t}"))
                    ));
                }
                Some(_) => {}
                None => {
                    seen.insert(bits, &case.value);
                }
            }
        }
    }
    errors
}

/// The unique definition of `value` in `func`, when there is exactly one.
fn unique_def<'f>(defs: &BTreeMap<u32, Vec<&'f Inst>>, value: ValueId) -> Option<&'f Inst> {
    match defs.get(&value.index())?.as_slice() {
        [only] => Some(*only),
        _ => None,
    }
}

/// One widening step between the tag lane and the selector, applied from the
/// tag outward.
#[derive(Clone, Copy)]
enum Widen {
    /// `zext` / equal-width `bitcast`: the bits carry over, zero-extended.
    Zero { to: u32 },
    /// `sext` from `from` bits: the top bit is replicated.
    Sign { from: u32, to: u32 },
}

/// A selector traced to the enum tag it reads.
struct TagSelector<'m> {
    def: &'m EnumDef,
    enum_ty: String,
    /// The widening casts from the tag lane to the selector, innermost first.
    widen: Vec<Widen>,
    /// The width the switch compares its cases at (the selector's).
    width: u32,
}

impl TagSelector<'_> {
    /// The selector value a variant with discriminant `disc` produces: its
    /// bits at the tag width `tag_bits`, then each cast in turn — exactly
    /// what the reference interpreter's `ExtractField` + `Cast` compute.
    fn selector_bits_of(&self, disc: i128, tag_bits: u32) -> u128 {
        let mut bits = mask(disc as u128, tag_bits);
        for step in &self.widen {
            bits = match *step {
                Widen::Zero { to } => mask(bits, to),
                Widen::Sign { from, to } => {
                    let negative = from > 0 && from < 128 && (bits >> (from - 1)) & 1 == 1;
                    let extended = if negative {
                        bits | !mask(u128::MAX, from)
                    } else {
                        bits
                    };
                    mask(extended, to)
                }
            };
        }
        bits
    }
}

/// Resolve a selector to the enum value whose tag it reads: its definition,
/// through any number of `Copy`s and value-preserving integer widenings
/// (`zext`, `sext`, equal-width `bitcast` — the Trust bridge's
/// `Rvalue::Discriminant` lowering widens the canonical tag to the MIR
/// discriminant type with exactly one of these), is `ExtractField { field: 0 }`
/// of a `Ty::Enum` value whose tag lane is at the width the chain starts
/// from. `None` = provenance not resolvable (rule 1 alone): a narrowing or
/// any other operation breaks the chain.
fn selector_enum<'m>(
    module: &'m Module,
    defs: &BTreeMap<u32, Vec<&Inst>>,
    val_ty: &BTreeMap<u32, Ty>,
    selector: ValueId,
) -> Option<TagSelector<'m>> {
    let pointer_bits = module.pointer_bits();
    let width = selector_width(val_ty.get(&selector.index())?, pointer_bits)?;
    let mut current = selector;
    // Collected outermost first; reversed once the tag is reached.
    let mut widen: Vec<Widen> = Vec::new();
    // The width the next-inner value must have for the chain to be exact.
    let mut expect = width;
    // Each step moves to an operand's definition; a well-formed SSA chain is
    // at most as long as the function has definitions, a cyclic one (itself
    // refused) must not spin.
    for _ in 0..=defs.len() {
        match unique_def(defs, current)? {
            Inst::Copy { operand, .. } => current = *operand,
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => {
                let from = selector_width(src_ty, pointer_bits)?;
                let to = selector_width(dst_ty, pointer_bits)?;
                if to != expect {
                    return None;
                }
                let step = match op {
                    CastOp::ZExt if to >= from => Widen::Zero { to },
                    CastOp::SExt if to >= from => Widen::Sign { from, to },
                    CastOp::Bitcast if to == from => Widen::Zero { to },
                    _ => return None,
                };
                widen.push(step);
                expect = from;
                current = *operand;
            }
            Inst::ExtractField {
                aggregate,
                field: 0,
                ..
            } => {
                let enum_ty = val_ty.get(&aggregate.index())?;
                let Ty::Enum(id) = enum_ty else {
                    return None;
                };
                let def = module.enum_def(*id)?;
                let tag_bits = def.canonical_tag_repr()?.ty().bit_width()?;
                if tag_bits != expect {
                    return None;
                }
                widen.reverse();
                return Some(TagSelector {
                    def,
                    enum_ty: format!("{enum_ty}"),
                    widen,
                    width,
                });
            }
            _ => return None,
        }
    }
    None
}

/// Rule 2 (module-level): a flagged `Switch` whose selector reads an enum's tag
/// covers every variant the validator cannot prove uninhabited, and names no
/// value that is not a discriminant. See the module doc.
pub(super) fn validate_exhaustive_switch_cases(
    layouts: &trust_ir::LayoutTable<'_>,
    func: &Function,
    val_ty: &BTreeMap<u32, Ty>,
) -> Vec<ValidationError> {
    let module = layouts.module();
    let mut errors = Vec::new();
    let flagged = func.blocks.iter().any(|b| {
        b.terminator().is_some_and(|t| {
            matches!(
                t.inst,
                Inst::Switch {
                    exhaustive_enum_unreachable: true,
                    ..
                }
            )
        })
    });
    if !flagged {
        return errors;
    }
    let mut defs: BTreeMap<u32, Vec<&Inst>> = BTreeMap::new();
    for block in &func.blocks {
        for node in &block.body {
            for result in &node.results {
                defs.entry(result.index()).or_default().push(&node.inst);
            }
        }
    }
    for block in &func.blocks {
        let Some(term) = block.terminator() else {
            continue;
        };
        let Inst::Switch {
            value,
            cases,
            exhaustive_enum_unreachable: true,
            ..
        } = &term.inst
        else {
            continue;
        };
        let Some(sel) = selector_enum(module, &defs, val_ty, *value) else {
            continue;
        };
        let def = sel.def;
        // `selector_enum` resolved the canonical tag repr; the discriminants
        // it is computed from resolve with it.
        let (Some(discs), Some(tag_bits)) = (
            def.effective_discriminants(),
            def.canonical_tag_repr().and_then(|r| r.ty().bit_width()),
        ) else {
            continue;
        };
        let block_id = block.id.index();
        let enum_ty = sel.enum_ty.clone();
        let mut refuse = |reason: String| {
            errors.push(ValidationError::ExhaustiveSwitchCasesIncomplete {
                block: block_id,
                enum_ty: enum_ty.clone(),
                reason,
            });
        };
        let disc_bits: Vec<u128> = discs
            .iter()
            .map(|d| sel.selector_bits_of(*d, tag_bits))
            .collect();
        let mut covered: BTreeSet<u128> = BTreeSet::new();
        for case in cases {
            match case_bits(sel.width, &case.value) {
                Some(bits) if disc_bits.contains(&bits) => {
                    covered.insert(bits);
                }
                _ => refuse(format!(
                    "case value {} is not a discriminant of {}",
                    case.value, sel.enum_ty
                )),
            }
        }
        let missing: Vec<String> = def
            .variants
            .iter()
            .zip(discs.iter().zip(&disc_bits))
            .filter(|(_, (_, bits))| !covered.contains(bits))
            // The repo's ONE uninhabitedness predicate (WS3.14): the same
            // answer that refuses constructing the variant
            // (`UninhabitedVariantConstructed`), exempts it from niche
            // coverage, and makes the interpreter refuse decoding it — so an
            // omitted variant is exempt here exactly when no value of it can
            // exist anywhere else in the format.
            .filter(|(variant, _)| !layouts.variant_is_uninhabited(variant))
            .map(|(variant, (disc, _))| format!("{} = {disc}", variant.name))
            .collect();
        if !missing.is_empty() {
            refuse(format!(
                "no case for inhabited variant(s) {{{}}}, so the default arm is reachable",
                missing.join(", ")
            ));
        }
    }
    errors
}
