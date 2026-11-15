// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact actual ordinary match arm retained byte-for-byte as test oracle only.
use super::*;
pub(super) fn original(module: &Module, physical: usize, selected: usize) -> Vec<ValidationError> {
    let func = &module.functions[0];
    let mut errors = Vec::new();
    let val_ty = build_module_value_types(func, module);
    let closure_targets = local_closure_constant_targets(func);
    let function_catalog = ModuleFunctionCatalog::new(module);
    let nominal_types = Some(module.nominal_type_reachability());
    let pointer = StaticFunctionPointerAnalysis::new(func);
    let fn_pointer_analysis = Some(&pointer);
    for (block_at, block) in func.blocks.iter().enumerate() {
        let block_id = block.id.index();
        for (instruction_index, node) in block.body.iter().enumerate() {
            if physical != block_at || selected != instruction_index {
                continue;
            }
            match &node.inst {
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
                _=>{}
            }
        }
    }
    errors
}
