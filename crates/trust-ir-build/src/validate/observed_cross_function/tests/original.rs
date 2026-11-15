// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Whole retained actual ordinary closure, with test-only input bindings.
use super::*;
pub(super) fn run(
    module: &Module,
    physical: usize,
    dialect_schemas: Option<&DialectSchemaRegistry>,
) -> Vec<ValidationError> {
    let layouts = module.layout_table();
    let function_catalog = ModuleFunctionCatalog::new(module);
    let (_, census) = validate_type_table_references(module, &registry());
    let nominal_types =
        (census.dialect || census.handle).then(|| module.nominal_type_reachability());
    let func = &module.functions[physical];
    let analysis = StaticFunctionPointerAnalysis::new(func);
    let validate_cross_function =
        |func: &Function, fn_pointer_analysis: StaticPointerAnalysisRef<'_, '_>| {
            let mut errors = Vec::new();
            let func_ty = get_func_ty(module, &func.name, func.ty, &mut errors);
            let val_ty = build_module_value_types(func, module);
            // WS3.6: the tag-switch guard state a handle-bearing enum lane
            // read is decided against. Built only for a handle-bearing module
            // whose function actually reads a non-tag lane; when it is absent
            // such a read is REFUSED, never admitted.
            let handle_enum_guards = (census.handle
                && nominal_types.is_some()
                && HandleEnumGuards::function_reads_a_non_tag_lane(func))
            .then(|| HandleEnumGuards::new(func));
            // WS3.7: the sealed-slot state a handle `Alloca` / `Load` /
            // `Store` is decided against. Built only for a handle-bearing
            // module whose function allocates a slot reaching a handle; when
            // it is absent every such access is REFUSED, never admitted.
            let handle_slots = match &nominal_types {
                Some(nominal_types)
                    if census.handle
                        && handle_slots::SealedHandleSlots::function_allocates_a_handle(
                            func,
                            nominal_types,
                        ) =>
                {
                    Some(handle_slots::SealedHandleSlots::new(
                        &layouts,
                        func,
                        nominal_types,
                    ))
                }
                _ => None,
            };
            let closure_targets = local_closure_constant_targets(func);
            // WS2.7 (a): memory-effect attributes against the body, with the
            // module's callee attributes (see Pass 8 of the per-function pass).
            errors.extend(claims::validate_func_attr_claims(func, Some(module)));
            // WS2.6 rule 2: a flagged switch over an enum's tag covers the enum.
            errors.extend(exhaustive_switch::validate_exhaustive_switch_cases(
                &layouts, func, &val_ty,
            ));

            // audit #6: a body-bearing function's entry-block parameters must match
            // the declared `FuncTy::params` (count + types). Bodyless external
            // declarations have no entry block to compare.
            if let Some(func_ty) = func_ty
                && !func.blocks.is_empty()
                && let Some(entry_block) = func.blocks.iter().find(|b| b.id == func.entry)
            {
                let entry_param_tys: Vec<Ty> = entry_block
                    .params
                    .iter()
                    .map(|(_, ty)| ty.clone())
                    .collect();
                // Refine-involving positions are decided by `validate_refinements`,
                // which compares REPRESENTATIONS and then the predicate implication
                // in the sound direction (a body may only assume what the signature
                // guarantees) and names both predicates on failure. Raw equality is
                // the wrong question for them — see `check_block_arg_types`.
                let arity_matches = entry_param_tys.len() == func_ty.params.len();
                let non_refine_types_match = entry_param_tys
                    .iter()
                    .zip(func_ty.params.iter())
                    .all(|(a, b)| a == b || a.is_refine() || b.is_refine());
                if !arity_matches || !non_refine_types_match {
                    errors.push(ValidationError::EntryParamsMismatch {
                        func_name: func.name.clone(),
                        expected: format_ty_list(&func_ty.params),
                        actual: format_ty_list(&entry_param_tys),
                    });
                }
            }

            for block in &func.blocks {
                let block_id = block.id.index();

                for (instruction_index, node) in block.body.iter().enumerate() {
                    if let Some(nominal_types) = &nominal_types {
                        validate_nominal_instruction_types(
                            module,
                            node,
                            &val_ty,
                            nominal_types,
                            block.id,
                            instruction_index,
                            handle_enum_guards.as_ref(),
                            handle_slots.as_ref(),
                            &func.name,
                            &mut errors,
                        );
                    }
                    match &node.inst {
                        // Amendment D (§20): the place is passed to the glue
                        // as a `Call` passes a `Ptr` argument, so its type is
                        // exactly `Ptr` (a refined pointer whose
                        // representation is `Ptr` included). Before §20 a
                        // drop's operand was never checked at all.
                        Inst::Drop { ptr, .. } | Inst::DropInvoke { ptr, .. } => {
                            if let Some(actual) = val_ty.get(&ptr.index())
                                && module.representation_ty(actual) != Some(&Ty::Ptr)
                            {
                                errors.push(ValidationError::OperandTypeMismatch {
                                    block: block_id,
                                    op: instruction_kind(&node.inst).to_string(),
                                    role: "ptr".to_string(),
                                    expected: "ptr".to_string(),
                                    actual: format!("{actual}"),
                                });
                            }
                        }
                        Inst::Return { values } => {
                            if let Some(func_ty) = func_ty {
                                check_return_values(
                                    block_id,
                                    values,
                                    func_ty,
                                    &val_ty,
                                    &mut errors,
                                );
                            }
                        }
                        // A suspend IS a return of `value` to the resumer
                        // (`GEP` + `Store` + `Return(value)` by definition), so
                        // it is held to the signature by the SAME check as
                        // `Return`, with `values = [value]`: exactly one return
                        // slot, and the yielded value has its type (refinements
                        // decided by `validate_refinements`, where the yield is
                        // a `ReturnValues` site exactly like a return operand).
                        // Without this a `-> handle<..>` function could yield a
                        // `Ptr` — a forged handle the v43 origin rule never
                        // sees, because nothing on the node is handle-typed
                        // (F-028). `frame` is checked by `validate_types`.
                        Inst::CoroSuspend { value, .. } => {
                            if let Some(func_ty) = func_ty {
                                check_return_values(
                                    block_id,
                                    &[*value],
                                    func_ty,
                                    &val_ty,
                                    &mut errors,
                                );
                            }
                        }
                        Inst::Call { callee, args } | Inst::CallCannotUnwind { callee, args } => {
                            let Some(callee_func) = function_catalog.unique(*callee) else {
                                errors.push(ValidationError::CalleeNotFound {
                                    block: block_id,
                                    callee_id: callee.index(),
                                });
                                continue;
                            };

                            let Some(callee_ty) =
                                get_func_ty(module, &callee_func.name, callee_func.ty, &mut errors)
                            else {
                                continue;
                            };

                            let expected_arg_count = callee_ty.params.len();
                            let actual_arg_count = args.len();
                            let arg_count_mismatch = if callee_ty.is_vararg {
                                validate_nominal_varargs(
                                    args,
                                    expected_arg_count,
                                    &val_ty,
                                    nominal_types.as_ref(),
                                    &func.name,
                                    &mut errors,
                                );
                                actual_arg_count < expected_arg_count
                            } else {
                                actual_arg_count != expected_arg_count
                            };

                            if arg_count_mismatch {
                                errors.push(ValidationError::CallArgCountMismatch {
                                    block: block_id,
                                    callee: callee_func.name.clone(),
                                    expected: expected_arg_count,
                                    actual: actual_arg_count,
                                    caller_producer: func
                                        .producer
                                        .as_ref()
                                        .map(ToString::to_string),
                                    callee_producer: callee_func
                                        .producer
                                        .as_ref()
                                        .map(ToString::to_string),
                                });
                            }

                            for (arg_index, (arg, expected_ty)) in
                                args.iter().zip(callee_ty.params.iter()).enumerate()
                            {
                                if let Some(actual_ty) = val_ty.get(&arg.index())
                                && actual_ty != expected_ty
                                // See `check_block_arg_types`: refine-involving
                                // edges are decided by `validate_refinements`.
                                && !(actual_ty.is_refine() || expected_ty.is_refine())
                                {
                                    errors.push(ValidationError::CallArgTypeMismatch {
                                        block: block_id,
                                        callee: callee_func.name.clone(),
                                        arg_index,
                                        expected: format!("{expected_ty}"),
                                        actual: format!("{actual_ty}"),
                                        caller_producer: func
                                            .producer
                                            .as_ref()
                                            .map(ToString::to_string),
                                        callee_producer: callee_func
                                            .producer
                                            .as_ref()
                                            .map(ToString::to_string),
                                    });
                                }
                            }
                        }
                        // Amendment P (V1-V5): a panic site's entry is resolved
                        // and typed as a callee is, and its location checked.
                        Inst::Assert {
                            kind,
                            site: Some(site),
                            ..
                        }
                        | Inst::AssertInvoke { kind, site, .. } => {
                            validate_panic_site(
                                module,
                                &function_catalog,
                                func,
                                block_id,
                                instruction_index,
                                kind,
                                site,
                                &val_ty,
                                &mut errors,
                            );
                        }
                        // Invoke is a call with an unwind edge: its static callee
                        // gets the same existence/arity/type checks as a direct
                        // Call (the B5.1 scope rule relies on this callee id).
                        Inst::Invoke { callee, args, .. } => {
                            let Some(callee_func) = function_catalog.unique(*callee) else {
                                errors.push(ValidationError::CalleeNotFound {
                                    block: block_id,
                                    callee_id: callee.index(),
                                });
                                continue;
                            };

                            let Some(callee_ty) =
                                get_func_ty(module, &callee_func.name, callee_func.ty, &mut errors)
                            else {
                                continue;
                            };

                            let expected_arg_count = callee_ty.params.len();
                            let actual_arg_count = args.len();
                            let arg_count_mismatch = if callee_ty.is_vararg {
                                validate_nominal_varargs(
                                    args,
                                    expected_arg_count,
                                    &val_ty,
                                    nominal_types.as_ref(),
                                    &func.name,
                                    &mut errors,
                                );
                                actual_arg_count < expected_arg_count
                            } else {
                                actual_arg_count != expected_arg_count
                            };

                            if arg_count_mismatch {
                                errors.push(ValidationError::CallArgCountMismatch {
                                    block: block_id,
                                    callee: callee_func.name.clone(),
                                    expected: expected_arg_count,
                                    actual: actual_arg_count,
                                    caller_producer: func
                                        .producer
                                        .as_ref()
                                        .map(ToString::to_string),
                                    callee_producer: callee_func
                                        .producer
                                        .as_ref()
                                        .map(ToString::to_string),
                                });
                            }

                            for (arg_index, (arg, expected_ty)) in
                                args.iter().zip(callee_ty.params.iter()).enumerate()
                            {
                                if let Some(actual_ty) = val_ty.get(&arg.index())
                                    && actual_ty != expected_ty
                                {
                                    errors.push(ValidationError::CallArgTypeMismatch {
                                        block: block_id,
                                        callee: callee_func.name.clone(),
                                        arg_index,
                                        expected: format!("{expected_ty}"),
                                        actual: format!("{actual_ty}"),
                                        caller_producer: func
                                            .producer
                                            .as_ref()
                                            .map(ToString::to_string),
                                        callee_producer: callee_func
                                            .producer
                                            .as_ref()
                                            .map(ToString::to_string),
                                    });
                                }
                            }
                        }
                        Inst::SeqMap { ty, fwd, .. } => {
                            // Well-formedness: the element function must exist and be
                            // the single-`&mut` element form `fn(&mut elem)` over the
                            // sequence's element type (its Aeneas forward view is
                            // elem -> elem). Fail-closed on unresolvable types.
                            let Some(fwd_func) = function_catalog.unique(*fwd) else {
                                errors.push(ValidationError::SeqMapFwdNotFound {
                                    block: block_id,
                                    fwd_id: fwd.index(),
                                });
                                continue;
                            };
                            let Some(fwd_ty) =
                                get_func_ty(module, &fwd_func.name, fwd_func.ty, &mut errors)
                            else {
                                continue;
                            };
                            let elem = match ty {
                                Ty::Sequence(elem_id) => module.ty(*elem_id).cloned(),
                                _ => None,
                            };
                            let Some(elem) = elem else {
                                errors.push(ValidationError::SeqMapTypeNotSequence {
                                    block: block_id,
                                    ty: format!("{ty}"),
                                });
                                continue;
                            };
                            let sig_ok = fwd_ty.returns.is_empty()
                                && !fwd_ty.is_vararg
                                && fwd_ty.params.len() == 1
                                && matches!(&fwd_ty.params[0], Ty::RefMut(p) if **p == elem);
                            if !sig_ok {
                                let actual_params = fwd_ty
                                    .params
                                    .iter()
                                    .map(|t| format!("{t}"))
                                    .collect::<Vec<_>>()
                                    .join(", ");
                                let actual_returns = fwd_ty
                                    .returns
                                    .iter()
                                    .map(|t| format!("{t}"))
                                    .collect::<Vec<_>>()
                                    .join(", ");
                                errors.push(ValidationError::SeqMapFwdSignatureMismatch {
                                    block: block_id,
                                    fwd: fwd_func.name.clone(),
                                    expected: format!("fn(&mut {elem})"),
                                    actual: format!("fn({actual_params}) -> ({actual_returns})"),
                                });
                            }
                        }
                        Inst::CallIndirect {
                            callee,
                            sig,
                            args,
                            calling_conv,
                        }
                        | Inst::CallIndirectCannotUnwind {
                            callee,
                            sig,
                            args,
                            calling_conv,
                        }
                        // Amendment D, Part 2: `InvokeIndirect` takes
                        // `CallIndirect`'s callee, signature, argument and
                        // convention checks verbatim; its edges are checked
                        // with the other terminators'.
                        | Inst::InvokeIndirect {
                            callee,
                            sig,
                            args,
                            calling_conv,
                            ..
                        } => {
                            let Some(sig_ty) = module.func_types.get(sig.as_usize()) else {
                                errors.push(ValidationError::CallIndirectSigNotFound {
                                    block: block_id,
                                    sig_id: sig.index(),
                                });
                                continue;
                            };
                            if let Some(abi) = &sig_ty.abi
                                && abi.lowered_convention != *calling_conv
                            {
                                errors.push(ValidationError::InvalidSignatureAbi {
                                    signature: sig.index(),
                                    detail: format!("indirect edge in {} bb{block_id} changes the typed calling convention", func.name),
                                });
                            }

                            // Same rule as `validate_rust_abi_is_not_variadic`,
                            // on the indirect edge: a call site that declares
                            // the Rust convention over a variadic signature is
                            // the unknown-signature pattern, and it voids the
                            // arity/arg-type checks immediately below.
                            if sig_ty.is_vararg
                                && matches!(calling_conv, trust_ir::CallingConv::Rust)
                            {
                                errors.push(ValidationError::RustAbiVararg {
                                    function: func.id.index(),
                                    detail: format!(
                                        "indirect call edge in bb{block_id} declares the Rust \
                                         calling convention over variadic functy.{} ({} fixed \
                                         parameter(s))",
                                        sig.index(),
                                        sig_ty.params.len()
                                    ),
                                });
                            }

                            let expected_arg_count = sig_ty.params.len();
                            let actual_arg_count = args.len();
                            let arg_count_mismatch = if sig_ty.is_vararg {
                                validate_nominal_varargs(
                                    args,
                                    expected_arg_count,
                                    &val_ty,
                                    nominal_types.as_ref(),
                                    &func.name,
                                    &mut errors,
                                );
                                actual_arg_count < expected_arg_count
                            } else {
                                actual_arg_count != expected_arg_count
                            };

                            if arg_count_mismatch {
                                errors.push(ValidationError::CallIndirectArgCountMismatch {
                                    block: block_id,
                                    sig_id: sig.index(),
                                    expected: expected_arg_count,
                                    actual: actual_arg_count,
                                });
                            }

                            for (arg_index, (arg, expected_ty)) in
                                args.iter().zip(sig_ty.params.iter()).enumerate()
                            {
                                if let Some(actual_ty) = val_ty.get(&arg.index())
                                && actual_ty != expected_ty
                                // WP-1B/G1: a refine-involving argument is
                                // decided by `validate_refinements` against
                                // the DECLARED signature, naming both
                                // predicates. See `check_block_arg_types`.
                                && !decided_by_the_consumption_rule(actual_ty, expected_ty)
                                {
                                    errors.push(ValidationError::CallIndirectArgTypeMismatch {
                                        block: block_id,
                                        sig_id: sig.index(),
                                        arg_index,
                                        expected: format!("{expected_ty}"),
                                        actual: format!("{actual_ty}"),
                                    });
                                }
                            }

                            // G18-2: a `Ty::Closure` callee. This arm is
                            // ADDITIVE — it fires only when the callee's type is
                            // a closure type, and the `Ty::Func` rules above ran
                            // verbatim on the same node. `args` were already
                            // checked against `sig_ty`, which for a closure edge
                            // is the closure's APPARENT signature; the captured
                            // environment is not in `args`, it is supplied by the
                            // ABI (see `Interpreter::execute_closure_call`).
                            if let Some(Ty::Closure(closure_ty_id)) = val_ty.get(&callee.index()) {
                                match module.closure_type(*closure_ty_id) {
                                    None => {
                                        errors.push(ValidationError::ClosureTypeNotFound {
                                            location: format!(
                                                "function '{}' bb{block_id}",
                                                func.name
                                            ),
                                            closure_ty_id: closure_ty_id.index(),
                                        });
                                    }
                                    Some(closure_ty) => {
                                        if closure_ty.func != *sig {
                                            errors.push(
                                                ValidationError::CallIndirectClosureSigMismatch {
                                                    block: block_id,
                                                    closure_ty_id: closure_ty_id.index(),
                                                    declared_sig_id: sig.index(),
                                                    apparent_sig_id: closure_ty.func.index(),
                                                },
                                            );
                                        } else if let Some(target) =
                                            closure_targets.get(&callee.index())
                                            && let Some(target_func) =
                                                function_catalog.unique(*target)
                                            && let Some(target_ty) =
                                                module.func_types.get(target_func.ty.as_usize())
                                        {
                                            // The physical contract, derived from
                                            // the DECLARED closure type alone:
                                            // captures ++ apparent params ->
                                            // apparent returns.
                                            let expected_params: Vec<Ty> = closure_ty
                                                .captures
                                                .iter()
                                                .cloned()
                                                .chain(sig_ty.params.iter().cloned())
                                                .collect();
                                            if target_ty.is_vararg
                                                || target_ty.params != expected_params
                                                || target_ty.returns != sig_ty.returns
                                            {
                                                errors.push(
                                                    ValidationError::CallIndirectClosureTargetMismatch {
                                                        block: block_id,
                                                        closure_ty_id: closure_ty_id.index(),
                                                        target: target_func.name.clone(),
                                                        expected: format!(
                                                            "{}) -> ({}",
                                                            format_ty_list(&expected_params),
                                                            format_ty_list(&sig_ty.returns)
                                                        ),
                                                        actual: format!(
                                                            "{}) -> ({}",
                                                            format_ty_list(&target_ty.params),
                                                            format_ty_list(&target_ty.returns)
                                                        ),
                                                    },
                                                );
                                            }
                                        }
                                    }
                                }
                            }

                            // ABI pinning: where the function pointer's provenance
                            // is statically visible, the
                            // edge's DECLARED ABI must agree with the callee-side
                            // DECLARATION — both the calling convention and the
                            // structural signature (the latter is what rejects a
                            // by-value vs byval/sret aggregate-passing
                            // disagreement). Dynamically-flowing pointers are not
                            // statically checkable and are trusted as declared.
                            if let Some(resolution) = fn_pointer_analysis.and_then(|analysis| {
                                analysis.resolve_typed_at(*callee, block.id, instruction_index)
                            }) {
                                debug_assert_eq!(resolution.containing_function(), func.id);
                                let Some(callee_func) =
                                    function_catalog.unique(resolution.function())
                                else {
                                    // A successful function-local provenance
                                    // result does not authorize selecting a missing
                                    // or duplicate module declaration.
                                    errors.push(ValidationError::CalleeNotFound {
                                        block: block_id,
                                        callee_id: resolution.function().index(),
                                    });
                                    continue;
                                };
                                if *calling_conv != callee_func.calling_conv {
                                    errors.push(ValidationError::CallEdgeConvMismatch {
                                        block: block_id,
                                        callee: callee_func.name.clone(),
                                        declared: calling_conv.to_string(),
                                        actual: callee_func.calling_conv.to_string(),
                                    });
                                }
                                if let Some(callee_ty) =
                                    module.func_types.get(callee_func.ty.as_usize())
                                    && (resolution.declared_signature() != *sig
                                        || resolution.declared_signature() != callee_func.ty
                                        || sig_ty != callee_ty)
                                {
                                    errors.push(ValidationError::CallEdgeSignatureMismatch {
                                        block: block_id,
                                        callee: callee_func.name.clone(),
                                        declared: format!(
                                            "call functy.{} ({}) -> ({}); FnDef declares functy.{}",
                                            sig.index(),
                                            format_ty_list(&sig_ty.params),
                                            format_ty_list(&sig_ty.returns),
                                            resolution.declared_signature().index(),
                                        ),
                                        actual: format!(
                                            "target functy.{} ({}) -> ({})",
                                            callee_func.ty.index(),
                                            format_ty_list(&callee_ty.params),
                                            format_ty_list(&callee_ty.returns)
                                        ),
                                    });
                                }
                            }
                        }
                        // audit #1: ExtractField / InsertField need module
                        // aggregate definitions to check the field index range and
                        // the declared field type, so they are validated here (the
                        // per-function pass has no module tables).
                        Inst::ExtractField {
                            ty,
                            aggregate,
                            field,
                        } => {
                            validate_field_access(
                                &mut errors,
                                module,
                                block_id,
                                "extract_field",
                                *aggregate,
                                *field,
                                ty,
                                None,
                                &val_ty,
                            );
                        }
                        Inst::InsertField {
                            ty,
                            aggregate,
                            field,
                            value,
                        } => {
                            validate_field_access(
                                &mut errors,
                                module,
                                block_id,
                                "insert_field",
                                *aggregate,
                                *field,
                                ty,
                                Some(*value),
                                &val_ty,
                            );
                        }
                        // WS3.5 (F-049): the register-level aggregate seed.
                        // Every lane is an `InsertField`-grade write against
                        // the definition's lane type, so it needs the module
                        // tables exactly as the two projections above do.
                        Inst::MakeAggregate {
                            ty,
                            variant,
                            fields,
                        } => {
                            validate_make_aggregate(
                                &mut errors,
                                &layouts,
                                block_id,
                                ty,
                                *variant,
                                fields,
                                &val_ty,
                            );
                        }
                        // v50: `n` copies of one register value. The element
                        // type is a module `TyId`, so the rule needs the tables.
                        Inst::ArraySplat { ty, value } => {
                            validate_array_splat(
                                &mut errors,
                                module,
                                block_id,
                                ty,
                                *value,
                                &val_ty,
                            );
                        }
                        // audit #12: route EVERY registered dialect through
                        // validation, not just the vector dialect. Parsed /
                        // deserialized gpu/avx512/ane ops were previously never
                        // checked.
                        Inst::DialectOp(op) => {
                            validate_dialect_op(&mut errors, block_id, op, &val_ty);
                            if let Some(schemas) = dialect_schemas
                                && let Err(error) = schemas.validate_op_with_func_types(
                                    op,
                                    node.results.len(),
                                    |id| val_ty.get(&id.index()),
                                    |id| module.func_type(id),
                                )
                            {
                                errors.push(ValidationError::InvalidDialectSchema {
                                    block: block_id,
                                    op: op.qualified_name(),
                                    reason: error.to_string(),
                                });
                            }
                        }
                        _ => {}
                    }
                }
            }
            errors
        };

    validate_cross_function(
        func,
        function_has_indirect_call_fallback(func).then_some(&analysis),
    )
}
