// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact retained contiguous ordinary shape block; surrounding proof rules omitted.
use super::*;
pub(super) fn ordinary(
    module: &Module,
    func: &Function,
    summary: &FunctionSummary,
) -> Vec<ValidationError> {
    let mut errors = Vec::new();
    let signature = module.func_types.get(func.ty.index() as usize);
    let invalid = |detail: String| ValidationError::InvalidFunctionSummary {
        function: func.id.index(),
        detail,
    };
    let has_clauses = !summary.requires.is_empty()
        || !summary.ensures.is_empty()
        || !summary.decreases.is_empty();
    if (has_clauses || !summary.params.is_empty())
        && let Some(ft) = signature
        && summary.params.len() != ft.params.len()
    {
        errors.push(invalid(format!(
            "summary lists {} parameter name(s) but the signature has {}",
            summary.params.len(),
            ft.params.len()
        )));
    }

    // v59 (WS1.14): the effect summary's SHAPE, on every function. Each set
    // has ONE spelling (so equality is set equality, which the cross-crate
    // restatement relies on) and names only places that exist here. Whether a
    // body honours the claim is `effects::validate_effect_summary`'s question.
    if let Some(effects) = &summary.effects {
        for (side, set) in [("reads", &effects.reads), ("writes", &effects.writes)] {
            if !set.is_canonical() {
                errors.push(invalid(format!(
                    "effects.{side} is not canonical: a Places set must be non-empty and \
                     strictly ascending (ParamPointee by index, then Global by id, no \
                     duplicate); spell the empty set Nothing"
                )));
            }
            for place in set.places() {
                match place {
                    trust_ir::EffectPlace::ParamPointee { index } => match signature {
                        Some(ft) if (*index as usize) < ft.params.len() => {}
                        Some(ft) => errors.push(invalid(format!(
                            "effects.{side} names the pointee of parameter {index} but the \
                             signature declares {} parameter(s)",
                            ft.params.len()
                        ))),
                        None => errors.push(invalid(format!(
                            "effects.{side} names the pointee of parameter {index}, but \
                             functy.{} is not declared in this module",
                            func.ty.index()
                        ))),
                    },
                    trust_ir::EffectPlace::Global(global) => {
                        if module.globals.get(global.as_usize()).is_none() {
                            errors.push(invalid(format!(
                                "effects.{side} names global #{}, which this module does not \
                                 declare",
                                global.index()
                            )));
                        }
                    }
                }
            }
        }
    }

    errors
}
