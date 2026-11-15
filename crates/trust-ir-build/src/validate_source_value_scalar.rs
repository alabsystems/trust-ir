// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Separate typed witness: mixed scalar equations cannot be passed to the
//! existing uniform UInt operational bridge through a shared public type.
use super::CheckedSourceValueEquation;
use clean_kernel::{Environment, Expr, Name};
use trust_ir::{Function, Module};

/// A checked mixed Bool/UInt source equation, bound to its borrowed inputs.
/// It exposes no conversion to the UInt operational witness or publication grant.
///
/// Both witness types can be used independently:
///
/// ```
/// use trust_ir_build::{CheckedScalarSourceValueEquation, CheckedSourceValueEquation};
/// fn keep_scalar<'a>(value: CheckedScalarSourceValueEquation<'a>)
///     -> CheckedScalarSourceValueEquation<'a> { value }
/// fn keep_word<'a>(value: CheckedSourceValueEquation<'a>)
///     -> CheckedSourceValueEquation<'a> { value }
/// ```
///
/// Promoting a scalar witness to the operational word witness is a type error:
///
/// ```compile_fail,E0308
/// use trust_ir_build::{CheckedScalarSourceValueEquation, CheckedSourceValueEquation};
/// fn cannot_promote<'a>(value: CheckedScalarSourceValueEquation<'a>) {
///     let _: CheckedSourceValueEquation<'a> = value;
/// }
/// ```
pub struct CheckedScalarSourceValueEquation<'a> {
    checked: CheckedSourceValueEquation<'a>,
}

impl<'a> CheckedScalarSourceValueEquation<'a> {
    pub(super) fn new(checked: CheckedSourceValueEquation<'a>) -> Self {
        Self { checked }
    }
    pub fn module(&self) -> &Module {
        self.checked.module()
    }
    pub fn function(&self) -> &Function {
        self.checked.function()
    }
    pub fn environment(&self) -> &Environment {
        self.checked.environment()
    }
    pub fn source(&self) -> &Name {
        self.checked.source()
    }
    pub fn judgment(&self) -> &Expr {
        self.checked.judgment()
    }
    pub fn proof(&self) -> &Expr {
        self.checked.proof()
    }
    pub fn source_closure_digest(&self) -> &[u8; 32] {
        self.checked.source_closure_digest()
    }
    pub fn equation_closure_digest(&self) -> &[u8; 32] {
        self.checked.equation_closure_digest()
    }
}
