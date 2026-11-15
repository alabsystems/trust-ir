// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact original first-loop body; ordinary helpers remain the independent oracle.
use super::*;
pub(super) fn oracle(
    module: &Module,
    func: &Function,
    summary: &FunctionSummary,
) -> Vec<ValidationError> {
    use trust_ir::proof::ClausePlace;
    let mut errors = Vec::new();
    let invalid = |detail: String| ValidationError::InvalidFunctionSummary {
        function: func.id.index(),
        detail,
    };

    let signature = module.func_types.get(func.ty.index() as usize);
    let defined_values = function_defined_values(func);
    // The SSA type map a `Value` binding is typed through; built at most once,
    // and only when a clause binds a `Value`.
    let mut value_types: Option<BTreeMap<u32, Ty>> = None;

    let mut clauses: Vec<(ContractClauseRole, usize, &trust_ir::ProofFormula)> = Vec::new();
    for (index, clause) in summary.requires.iter().enumerate() {
        clauses.push((ContractClauseRole::Requires, index, clause));
    }
    for (index, clause) in summary.ensures.iter().enumerate() {
        clauses.push((ContractClauseRole::Ensures, index, clause));
    }
    // `decreases` is a clause list like any other (v41): its measures are
    // `ProofFormula`s, so they route by schema and bind free names the same way.
    for (index, clause) in summary.decreases.iter().enumerate() {
        clauses.push((ContractClauseRole::Decreases, index, clause));
    }

    for (role, index, clause) in clauses {
        let clause_at = format!("{} clause {index}", role.name());
        if clause.schema.trim().is_empty() {
            errors.push(invalid(format!("{clause_at} has an empty schema")));
        }

        let mut bound_names: BTreeSet<&str> = BTreeSet::new();
        for (name, binding) in &clause.bindings {
            let at = format!("{clause_at} binding '{name}'");
            if name.trim().is_empty() {
                errors.push(invalid(format!(
                    "{clause_at} binds a blank free name, which can never be the name of a \
                     variable in the clause"
                )));
            }
            if !bound_names.insert(name.as_str()) {
                errors.push(invalid(format!(
                    "{at} is bound more than once; `bindings` is a name -> (sort, place) map, so \
                     a repeated name leaves the clause's free variable ambiguous"
                )));
            }

            // Resolve the parameter index shared by `Param`, `MutParamExit`
            // and `ParamPointeeEntry` (all index `FuncTy::params`, per
            // `ClausePlace`'s own doc). The entry pointee is legal on every
            // role, as `Param` is.
            let param_index = match binding.place {
                ClausePlace::Param { index } | ClausePlace::ParamPointeeEntry { index } => {
                    Some(index)
                }
                ClausePlace::MutParamExit { index } => {
                    if role != ContractClauseRole::Ensures {
                        errors.push(invalid(format!(
                            "{at} uses MutParamExit, the give-back / primed-output place, on a {} \
                             clause; `ClausePlace` makes it legal only on an ensures clause",
                            role.name()
                        )));
                    }
                    Some(index)
                }
                _ => None,
            };
            if let Some(parameter) = param_index {
                match signature {
                    Some(ft) if (parameter as usize) < ft.params.len() => {}
                    Some(ft) => errors.push(invalid(format!(
                        "{at} names parameter {parameter} but the signature declares {} \
                         parameter(s)",
                        ft.params.len()
                    ))),
                    None => errors.push(invalid(format!(
                        "{at} cannot be resolved: functy.{} is not declared in this module, so \
                         the parameter arity it would be checked against is unknown",
                        func.ty.index()
                    ))),
                }
            }

            match binding.place {
                // Handled above.
                ClausePlace::Param { .. }
                | ClausePlace::MutParamExit { .. }
                | ClausePlace::ParamPointeeEntry { .. } => {}
                ClausePlace::ResultSlot { index: slot } => match signature {
                    Some(ft) if (slot as usize) < ft.returns.len() => {}
                    Some(ft) => errors.push(invalid(format!(
                        "{at} names result slot {slot} but the signature declares {} return \
                         value(s)",
                        ft.returns.len()
                    ))),
                    None => errors.push(invalid(format!(
                        "{at} cannot be resolved: functy.{} is not declared in this module, so \
                         the return arity it would be checked against is unknown",
                        func.ty.index()
                    ))),
                },
                // v59 (WS1.14): the legacy un-epoched world cannot say whether
                // it denotes the world before the call or after it, so a
                // `proved` clause that binds it states nothing a caller can
                // check. Unbindable there, as WS1.2 ruled; an unproved
                // summary may still carry it.
                ClausePlace::World => {
                    if summary.proved {
                        errors.push(invalid(format!(
                            "{at} names the legacy un-epoched World on a proved summary; it \
                             cannot say whether it is the world before or after the call, so \
                             the clause is unbindable — bind WorldPre (entry) or WorldPost \
                             (exit) instead"
                        )));
                    }
                }
                // v59: the entry epoch is meaningful on every role.
                ClausePlace::WorldPre => {}
                // v59: the exit epoch exists only once the call has returned.
                ClausePlace::WorldPost => {
                    if role != ContractClauseRole::Ensures {
                        errors.push(invalid(format!(
                            "{at} names WorldPost, the world at exit, on a {} clause; \
                             `ClausePlace` makes it legal only on an ensures clause",
                            role.name()
                        )));
                    }
                }
                ClausePlace::Unwind => {
                    if role == ContractClauseRole::Requires {
                        errors.push(invalid(format!(
                            "{at} names the in-flight unwind state on a requires clause; \
                             `ClausePlace` makes Unwind illegal there — a precondition is \
                             evaluated before the call, where no unwind is in flight"
                        )));
                    }
                }
                ClausePlace::Value(value) => {
                    if func.is_declaration() {
                        errors.push(invalid(format!(
                            "{at} names SSA value v{} on a body-less declaration, which has no \
                             body to resolve it in",
                            value.index()
                        )));
                    } else if !defined_values.contains(&value.index()) {
                        errors.push(invalid(format!(
                            "{at} names SSA value v{}, which this function's body never defines",
                            value.index()
                        )));
                    }
                }
                // v46: the spec-variable index space belongs to a SpecModule's
                // `vars`, and a function summary has no such space. Resolving
                // `SpecVar { index: 0 }` to parameter 0 because the numbers
                // match would let a spec clause be read as a contract about a
                // different thing, so it is refused by name.
                ClausePlace::SpecVar { .. } | ClausePlace::SpecVarNext { .. } => {
                    errors.push(invalid(format!(
                        "{at} names {}, a spec-machine state variable; that index space belongs \
                         to a SpecModule's `vars` and a function summary has none, so the \
                         binding can never be resolved here",
                        clause_place_label(&binding.place)
                    )));
                }
            }

            // Rule 5: the sort is a faithful reading of the place's IR type.
            if let Some(detail) = clause_binding_type_refusal(
                module,
                func,
                binding,
                &defined_values,
                &mut value_types,
            ) {
                errors.push(invalid(format!("{at} {detail}")));
            }
        }
    }

    errors
}
