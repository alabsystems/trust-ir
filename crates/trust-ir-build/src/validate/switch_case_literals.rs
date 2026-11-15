// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The shared source-literal contract for integer and character switches.

use super::{
    ConstantSymbols, ValidationError, build_module_value_types_with, validate_constant_shape,
};
use std::collections::BTreeMap;
use trust_ir::inst::{Inst, SwitchCase};
use trust_ir::{Function, Module, ModuleFunctionCatalog, Ty, ValueId};

/// Check only literals in actual `Switch` instructions, at the actual
/// selector's integer or `char` representation type. Uses the same constant
/// funnel and diagnostic ordering as module validation, including canonical
/// integer spelling and Unicode scalar validity.
///
/// This is a narrow source contract, NOT module validation or codegen
/// admission. An absent, ambiguous or non-integer selector type contributes
/// no literal error; its SSA/type/selector defects are other validator
/// responsibilities. Globals, `Inst::Const`, and all non-switch operations
/// are deliberately not checked here.
///
/// One module layout table, duplicate-aware function catalog and constant
/// symbol table are prepared for the entire scan. Each function's value-type
/// map is built at most once, and only if that function contains a switch.
/// Sparse direct-call IDs use catalog lookups, never repeated module scans.
pub fn codegen_switch_case_literal_errors(module: &Module) -> Vec<ValidationError> {
    let layouts = module.layout_table();
    let functions = ModuleFunctionCatalog::new(module);
    let symbols = ConstantSymbols::new(&layouts);
    let mut errors = Vec::new();
    for function in &module.functions {
        let mut context = FunctionSwitchCases::new(module, &functions, &symbols, function);
        for block in &function.blocks {
            for node in &block.body {
                if let Inst::Switch { value, cases, .. } = &node.inst {
                    let location = format!("function '{}' bb{}", function.name, block.id.index());
                    context.check(*value, cases, &location, &mut errors);
                }
            }
        }
    }
    errors
}

/// A function-local, lazy view borrowing the pass's shared module context.
/// The full validator calls `check` in its original interleaved Const/Switch
/// order; the bulk codegen front calls it only for actual switches.
pub(super) struct FunctionSwitchCases<'context, 'module> {
    module: &'module Module,
    functions: &'context ModuleFunctionCatalog<'module>,
    symbols: &'context ConstantSymbols<'module>,
    function: &'module Function,
    value_types: Option<BTreeMap<u32, Ty>>,
}

impl<'context, 'module> FunctionSwitchCases<'context, 'module> {
    pub(super) fn new(
        module: &'module Module,
        functions: &'context ModuleFunctionCatalog<'module>,
        symbols: &'context ConstantSymbols<'module>,
        function: &'module Function,
    ) -> Self {
        Self {
            module,
            functions,
            symbols,
            function,
            value_types: None,
        }
    }

    pub(super) fn check(
        &mut self,
        value: ValueId,
        cases: &[SwitchCase],
        location: &str,
        errors: &mut Vec<ValidationError>,
    ) {
        let module = self.module;
        let functions = self.functions;
        let function = self.function;
        let selector = self
            .value_types
            .get_or_insert_with(|| {
                build_module_value_types_with(function, |node| match &node.inst {
                    Inst::Call { callee, .. }
                    | Inst::CallCannotUnwind { callee, .. }
                    | Inst::Invoke { callee, .. } => functions
                        .unique(*callee)
                        .and_then(|callee| module.func_type(callee.ty))
                        .map(|ty| ty.returns.clone())
                        .unwrap_or_default(),
                    _ => node.result_tys(module),
                })
            })
            .get(&value.index())
            .and_then(|ty| module.representation_ty(ty))
            .filter(|ty| ty.is_integer() || matches!(ty, Ty::Char));
        let Some(selector) = selector else { return };
        for (index, case) in cases.iter().enumerate() {
            validate_constant_shape(
                module,
                functions,
                self.symbols,
                &case.value,
                selector,
                &format!("{location} switch case {index}"),
                errors,
            );
        }
    }
}

/// The same narrow actual-Switch literal contract under the caller's original
/// session/site. Operational stops return an error, never a smaller diagnostic
/// list. This creates no validated-module/codegen/proof/source capability.
pub fn codegen_switch_case_literal_errors_observed<O: trust_ir::interpret::ExecutionObserver>(
    module: &Module,
    session: &mut trust_ir::interpret::ObservedSession<'_, O>,
    site: trust_ir::interpret::ExecutionSite,
) -> Result<Vec<ValidationError>, trust_ir::interpret::ObservedValueError> {
    super::observed_const_shapes::codegen_switch_case_literal_errors_observed(module, session, site)
}
