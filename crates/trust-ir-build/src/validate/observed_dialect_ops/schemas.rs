// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use trust_ir::dialect::schema::{AttributeKind, OperandType, OperationSchema};
impl State<'_> {
    pub(super) fn schema<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        op: &DialectInst,
        result_count: usize,
        values: &ObservedValueTypes,
        registry: &DialectSchemaRegistry,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let schema = match registry.lookup_operation_observed(op, work.session, work.site)? {
            Ok(s) => s,
            Err(error) => {
                self.reason = error;
                return Ok(false);
            }
        };
        work.admit(4, size_of::<(usize, bool)>())?;
        let variadic = matches!(schema.operands.last(), Some(OperandType::VariadicExact(_)));
        let minimum = schema
            .operands
            .len()
            .checked_sub(usize::from(variadic))
            .ok_or(ObservedValueError::InvalidRange)?;
        if op.operands.len() != minimum && !(variadic && op.operands.len() > minimum) {
            self.head(
                if variadic {
                    "OperandCountAtLeast"
                } else {
                    "OperandCount"
                },
                work,
            )?;
            work.text(
                if variadic {
                    " { minimum: "
                } else {
                    " { expected: "
                },
                &mut self.reason,
            )?;
            work.unsigned(minimum as u128, &mut self.reason)?;
            work.text(", actual: ", &mut self.reason)?;
            work.unsigned(op.operands.len() as u128, &mut self.reason)?;
            work.text(" }", &mut self.reason)?;
            return Ok(false);
        }
        if !same_types(&op.result_tys, &schema.results, work)? {
            self.head("ResultTypes", work)?;
            return Ok(false);
        }
        work.admit(1, size_of::<bool>())?;
        if result_count != schema.results.len() {
            self.count("ResultCount", schema.results.len(), result_count, work)?;
            return Ok(false);
        }
        let mut at = 0;
        while let Some(id) = work.at(&op.operands, at)? {
            work.admit(2, size_of::<Option<&OperandType>>())?;
            let expected = schema
                .operand_type_at(at)
                .ok_or(ObservedValueError::InvalidRange)?;
            let Some(actual) = values.get_observed(*id, work.session, work.site)? else {
                self.head("UndefinedOperand(ValueId(", work)?;
                work.unsigned(u128::from(id.index()), &mut self.reason)?;
                work.text("))", &mut self.reason)?;
                return Ok(false);
            };
            match expected {
                OperandType::Exact(expected) | OperandType::VariadicExact(expected) => {
                    if !actual.structural_eq_observed(expected, work.session, work.site)? {
                        self.head("OperandType { index: ", work)?;
                        work.unsigned(at as u128, &mut self.reason)?;
                        work.text(", expected: ", &mut self.reason)?;
                        self.raw_ty(expected, work)?;
                        work.text(", actual: ", &mut self.reason)?;
                        self.raw_ty(actual, work)?;
                        work.text(" }", &mut self.reason)?;
                        return Ok(false);
                    }
                }
                OperandType::Function { params, returns } => {
                    if !self.function_operand(module, at, actual, params, returns, work)? {
                        return Ok(false);
                    }
                }
            }
            work.next(&mut at)?;
        }
        self.attributes(op, schema, work)
    }
    fn function_operand<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        index: usize,
        ty: &Ty,
        params: &[Ty],
        returns: &[Ty],
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(1, size_of::<Option<trust_ir::FuncTyId>>())?;
        let Ty::Func(id) = ty else {
            self.head("ExpectedFunctionOperand { index: ", work)?;
            work.unsigned(index as u128, &mut self.reason)?;
            work.text(", actual: ", &mut self.reason)?;
            self.raw_ty(ty, work)?;
            work.text(" }", &mut self.reason)?;
            return Ok(false);
        };
        let Some(actual) = work.at(&module.func_types, id.as_usize())? else {
            self.head("FunctionTypeUnavailable { index: ", work)?;
            work.unsigned(index as u128, &mut self.reason)?;
            work.text(", signature: FuncTyId(", &mut self.reason)?;
            work.unsigned(u128::from(id.index()), &mut self.reason)?;
            work.text(") }", &mut self.reason)?;
            return Ok(false);
        };
        work.admit(1, size_of::<bool>())?;
        if actual.is_vararg
            || !same_types(&actual.params, params, work)?
            || !same_types(&actual.returns, returns, work)?
        {
            self.head("FunctionSignature { index: ", work)?;
            work.unsigned(index as u128, &mut self.reason)?;
            work.text(", expected: FuncTyG { params: ", &mut self.reason)?;
            self.raw_types(params, work)?;
            work.text(", returns: ", &mut self.reason)?;
            self.raw_types(returns, work)?;
            work.text(
                ", is_vararg: false, abi: None }, actual: ",
                &mut self.reason,
            )?;
            self.raw_func(actual, work)?;
            work.text(" }", &mut self.reason)?;
            return Ok(false);
        }
        Ok(true)
    }
    fn attributes<O: ExecutionObserver>(
        &mut self,
        op: &DialectInst,
        schema: &OperationSchema,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut at = 0;
        while work.at(&schema.attributes, at)?.is_some() {
            work.reserve(&mut self.seen)?;
            work.admit(1, size_of::<bool>())?;
            self.seen.push(false);
            work.next(&mut at)?;
        }
        let mut at = 0;
        while let Some(attr) = work.at(&op.attrs, at)? {
            let mut found = None;
            let mut index = 0;
            while let Some(expected) = work.at(&schema.attributes, index)? {
                if work.eq(&attr.name, &expected.name)? {
                    found = Some((index, expected.kind));
                    break;
                }
                work.next(&mut index)?;
            }
            let Some((index, expected)) = found else {
                self.named("UnknownAttribute", &attr.name, work)?;
                return Ok(false);
            };
            work.admit(1, 2 * size_of::<bool>())?;
            let seen = self
                .seen
                .get_mut(index)
                .ok_or(ObservedValueError::InvalidRange)?;
            if *seen {
                self.named("DuplicateAttribute", &attr.name, work)?;
                return Ok(false);
            }
            *seen = true;
            work.admit(8, 2 * size_of::<AttributeKind>())?;
            let actual = kind(&attr.value);
            if expected != actual {
                self.head("AttributeType { name: ", work)?;
                work.quoted(&attr.name, &mut self.reason)?;
                work.text(", expected: ", &mut self.reason)?;
                work.text(kind_name(expected), &mut self.reason)?;
                work.text(", actual: ", &mut self.reason)?;
                work.text(kind_name(actual), &mut self.reason)?;
                work.text(" }", &mut self.reason)?;
                return Ok(false);
            }
            work.next(&mut at)?;
        }
        work.admit(1, size_of::<bool>())?;
        if op.attrs.len() != schema.attributes.len() {
            let mut at = 0;
            while let Some(attr) = work.at(&schema.attributes, at)? {
                let seen = work
                    .at(&self.seen, at)?
                    .ok_or(ObservedValueError::InvalidRange)?;
                if !*seen {
                    self.named("MissingAttribute", &attr.name, work)?;
                    return Ok(false);
                }
                work.next(&mut at)?;
            }
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(true)
    }
}
fn same_types<O: ExecutionObserver>(a: &[Ty], b: &[Ty], work: &mut Work<'_, '_, O>) -> R<bool> {
    work.admit(1, size_of::<bool>())?;
    if a.len() != b.len() {
        return Ok(false);
    }
    let mut at = 0;
    while let Some(a) = work.at(a, at)? {
        let b = work.at(b, at)?.ok_or(ObservedValueError::InvalidRange)?;
        if !a.structural_eq_observed(b, work.session, work.site)? {
            return Ok(false);
        }
        work.next(&mut at)?;
    }
    Ok(true)
}
fn kind(value: &AttrValue) -> AttributeKind {
    match value {
        AttrValue::I64(_) => AttributeKind::I64,
        AttrValue::U64(_) => AttributeKind::U64,
        AttrValue::F64(_) => AttributeKind::F64,
        AttrValue::Bool(_) => AttributeKind::Bool,
        AttrValue::Str(_) => AttributeKind::Str,
        AttrValue::Bytes(_) => AttributeKind::Bytes,
        AttrValue::Ty(_) => AttributeKind::Ty,
    }
}
fn kind_name(value: AttributeKind) -> &'static str {
    match value {
        AttributeKind::I64 => "I64",
        AttributeKind::U64 => "U64",
        AttributeKind::F64 => "F64",
        AttributeKind::Bool => "Bool",
        AttributeKind::Str => "Str",
        AttributeKind::Bytes => "Bytes",
        AttributeKind::Ty => "Ty",
    }
}
