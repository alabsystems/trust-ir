// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use trust_ir::proof::clause_typing::{
    ObservedClauseTypingError, clause_sort_admits_observed, resolve_clause_place_borrowed_observed,
};
pub(super) fn check<O: ExecutionObserver>(
    module: &Module,
    function: &Function,
    role: ContractClauseRole,
    index: usize,
    name: &str,
    binding: &ClauseBinding,
    values: &mut Option<ObservedValueTypes>,
    detail: &mut String,
    render: &mut Option<String>,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(11, size_of::<ClausePlace>() + size_of::<Option<&Ty>>())?;
    let ty = match binding.place {
        ClausePlace::World
        | ClausePlace::WorldPre
        | ClausePlace::WorldPost
        | ClausePlace::Unwind
        | ClausePlace::SpecVar { .. }
        | ClausePlace::SpecVarNext { .. } => return Ok(false),
        ClausePlace::Value(value) => {
            work.admit(1, size_of::<bool>())?;
            if function.blocks.is_empty() || !walk::defined(function, value, work)? {
                return Ok(false);
            }
            work.admit(1, size_of::<Option<ObservedValueTypes>>())?;
            if values.is_none() {
                // Retain the complete returned map before any later fallible
                // lookup, formatting, output allocation or publication.
                *values = Some(build_module_value_types_observed(
                    function,
                    module,
                    work.session,
                    work.site,
                )?);
            }
            let map = values.as_ref().ok_or(ObservedValueError::InvalidRange)?;
            match map.get_observed(value, work.session, work.site)? {
                Some(ty) => ty,
                None => {
                    binding_prefix(role, index, name, detail, work)?;
                    work.text(" names ", detail)?;
                    place_text(binding.place, detail, work)?;
                    work.text(
                        ", whose IR type the validator cannot infer, so its sort ",
                        detail,
                    )?;
                    sort_text(&binding.sort, detail, render, work)?;
                    work.text(" cannot be checked", detail)?;
                    return Ok(true);
                }
            }
        }
        ClausePlace::Param { .. }
        | ClausePlace::ResultSlot { .. }
        | ClausePlace::MutParamExit { .. }
        | ClausePlace::ParamPointeeEntry { .. } => {
            match resolve_clause_place_borrowed_observed(
                module,
                function.id,
                &binding.place,
                work.session,
                work.site,
            )? {
                Ok(ty) => ty,
                Err(ObservedClauseTypingError::MutParamExitNotMutable {
                    index: parameter,
                    ty,
                }) => {
                    binding_prefix(role, index, name, detail, work)?;
                    work.text(" uses MutParamExit on parameter ", detail)?;
                    work.number(parameter as u128, detail)?;
                    work.text(" of type ", detail)?;
                    ty_text(ty, detail, render, work)?;
                    work.text(", which is not a &mut / *mut: a by-value parameter has no exit value distinct from its entry value",detail)?;
                    return Ok(true);
                }
                Err(ObservedClauseTypingError::ParamPointeeNotReference {
                    index: parameter,
                    ty,
                }) => {
                    binding_prefix(role, index, name, detail, work)?;
                    work.text(" uses ParamPointeeEntry on parameter ", detail)?;
                    work.number(parameter as u128, detail)?;
                    work.text(" of type ", detail)?;
                    ty_text(ty, detail, render, work)?;
                    work.text(", which is not a & / &mut reference: a by-value parameter has no pointee, and a raw, untyped, fat or reference-counted pointer does not say its pointee exists at entry",detail)?;
                    return Ok(true);
                }
                Err(
                    ObservedClauseTypingError::ParamOutOfRange { .. }
                    | ObservedClauseTypingError::ResultOutOfRange { .. }
                    | ObservedClauseTypingError::SignatureUnresolved { .. },
                ) => return Ok(false),
                Err(ObservedClauseTypingError::FunctionUnresolved { function, matches }) => {
                    binding_prefix(role, index, name, detail, work)?;
                    work.text(" cannot be typed: owning function f", detail)?;
                    work.number(function.index() as u128, detail)?;
                    work.text(" does not resolve uniquely (", detail)?;
                    work.number(matches as u128, detail)?;
                    work.text(" functions carry that id)", detail)?;
                    return Ok(true);
                }
                // This branch called the resolver only with the four typed
                // signature places. Refusing an impossible changed helper
                // result is not a silent default type or accepting fallback.
                Err(
                    ObservedClauseTypingError::PlaceHasNoIrType(_)
                    | ObservedClauseTypingError::ValuePlaceUnsupported(_),
                ) => return Err(ObservedValueError::InvalidRange),
            }
        }
    };
    work.admit(4, size_of::<Option<u32>>())?;
    let pointer_bits = module
        .target_info
        .as_ref()
        .map(|target| target.pointer_size.saturating_mul(8));
    if clause_sort_admits_observed(&binding.sort, ty, pointer_bits, work.session, work.site)? {
        return Ok(false);
    }
    binding_prefix(role, index, name, detail, work)?;
    work.text(" has sort ", detail)?;
    sort_text(&binding.sort, detail, render, work)?;
    work.text(" but ", detail)?;
    place_text(binding.place, detail, work)?;
    work.text(" is ", detail)?;
    ty_text(ty, detail, render, work)?;
    work.admit(4, size_of::<bool>())?;
    if matches!(ty, Ty::Isize | Ty::Usize)
        && matches!(binding.sort, ClauseSort::BitVec(_))
        && pointer_bits.is_none()
    {
        work.text(", whose width is unknown without target_info", detail)?;
    }
    Ok(true)
}
fn sort_text<O: ExecutionObserver>(
    sort: &ClauseSort,
    detail: &mut String,
    render: &mut Option<String>,
    work: &mut Work<'_, '_, O>,
) -> R {
    work.admit(1, size_of::<Option<String>>())?;
    if render.is_some() {
        return Err(ObservedValueError::InvalidRange);
    }
    *render = Some(sort.debug_observed(work.session, work.site)?);
    copy_render(detail, render, work)
}
fn ty_text<O: ExecutionObserver>(
    ty: &Ty,
    detail: &mut String,
    render: &mut Option<String>,
    work: &mut Work<'_, '_, O>,
) -> R {
    work.admit(1, size_of::<Option<String>>())?;
    if render.is_some() {
        return Err(ObservedValueError::InvalidRange);
    }
    *render = Some(ty.display_observed(work.session, work.site)?);
    copy_render(detail, render, work)
}
fn copy_render<O: ExecutionObserver>(
    detail: &mut String,
    render: &mut Option<String>,
    work: &mut Work<'_, '_, O>,
) -> R {
    work.admit(1, size_of::<Option<&str>>())?;
    work.text(
        render.as_deref().ok_or(ObservedValueError::InvalidRange)?,
        detail,
    )?;
    work.step(size_of::<Option<String>>().saturating_add(1));
    if let Some(text) = render.take() {
        work.retire_text(text);
    }
    work.admit(1, 0)
}
