// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent consumers of exact UInt and mixed Bool/UInt source equations.
//! The caller supplies the expected original environment/source mapping. The
//! witness supplies a theorem declaration; its goal is checked against a fresh
//! judgment derived from the actual module, never used to derive that judgment.
//! This API authenticates neither source text/environment provenance nor the
//! denotation reader's relationship to operational IR semantics. It grants no
//! body license, proof status, runtime/ABI/NoUB or machine-code assurance.

use clean_kernel::{
    BinderInfo, ConstantKind, Declaration, DeclarationVerification, Environment, Expr, Level, Name,
};
use trust_ir::{FuncId, Function, Module, ModuleFunctionCatalog, Ty};

#[cfg(feature = "source-value-operational")]
use super::ModuleValidationReport;
use super::clean_backend_tv::{Sort, denote_function_with_catalog};
use super::{ValidationConfig, ValidationError, validate_module_with_config};

#[path = "validate_source_value_scalar.rs"]
mod scalar;
pub use scalar::CheckedScalarSourceValueEquation;

/// Refusal by the source-value component, without changing module verdicts.
#[derive(Debug)]
pub enum SourceValueEquationError {
    InvalidModule(Vec<ValidationError>),
    Unsupported(String),
    Rejected(String),
}

impl core::fmt::Display for SourceValueEquationError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidModule(errors) => write!(f, "source-value module rejection: {errors:?}"),
            Self::Unsupported(reason) => write!(f, "unsupported source-value equation: {reason}"),
            Self::Rejected(reason) => write!(f, "source-value equation rejection: {reason}"),
        }
    }
}

impl std::error::Error for SourceValueEquationError {}

/// A read-only check of one exact borrowed module/function/environment/source
/// pair. Private fields and the borrow prevent transfer to a mutated subject.
/// This is not serializable evidence or a license for any emitted body.
pub struct CheckedSourceValueEquation<'a> {
    module: &'a Module,
    // The exact successful PINNED whole-module pass, not reconstructed status
    // or authority transferred from an operationally similar module.
    #[cfg(feature = "source-value-operational")]
    validation: ModuleValidationReport<'a>,
    function: &'a Function,
    environment: &'a Environment,
    source: &'a Name,
    judgment: Expr,
    proof: &'a Expr,
    source_closure: [u8; 32],
    equation_closure: [u8; 32],
}

impl<'a> CheckedSourceValueEquation<'a> {
    #[cfg(feature = "source-value-operational")]
    pub(crate) fn validation_report(&self) -> &ModuleValidationReport<'a> {
        &self.validation
    }
    pub fn module(&self) -> &Module {
        #[cfg(feature = "source-value-operational")]
        debug_assert!(
            self.validation
                .validated_module()
                .is_some_and(|m| std::ptr::eq(m, self.module))
        );
        self.module
    }
    pub fn function(&self) -> &Function {
        self.function
    }
    pub fn environment(&self) -> &Environment {
        self.environment
    }
    pub fn source(&self) -> &Name {
        self.source
    }
    pub fn judgment(&self) -> &Expr {
        &self.judgment
    }
    pub fn proof(&self) -> &Expr {
        self.proof
    }
    pub fn source_closure_digest(&self) -> &[u8; 32] {
        &self.source_closure
    }
    pub fn equation_closure_digest(&self) -> &[u8; 32] {
        &self.equation_closure
    }
}

fn closed_monomorphic(e: &Expr) -> bool {
    !e.has_fvar_quick()
        && !e.has_expr_mvar_quick()
        && !e.has_level_mvar_quick()
        && !e.has_level_param_quick()
        && e.loose_bvar_range() == 0
}

/// Independently check a proposed UInt source-value theorem against the actual
/// selected IR body and an externally chosen original source/environment.
///
/// The complete module is validated under the canonical pinned configuration,
/// including all nonselected bodies. The existing sorted IR denotation reader
/// supplies the selected body, width, arity and call edges. Only a call-free,
/// uniform UInt8/16/32/64 signature with at most 64 arguments is supported.
/// Neither the witness's theorem name nor its claimed goal selects the source,
/// function, sorts, input order or denotation. A changed pair requires a new
/// check. Successful checking does not establish independent authentication of
/// the caller's original environment or a proof of the IR reader's semantics.
///
/// # Errors
/// Refuses invalid modules, unsupported source/IR signatures, different claimed
/// goals, open or ill-typed proofs, and every canonical certification-audit or
/// exact theorem-admission failure, including non-certifying import modes.
pub fn check_uint_source_value_equation<'a>(
    module: &'a Module,
    function_id: FuncId,
    original_environment: &'a Environment,
    expected_source: &'a Name,
    proposed: &'a Declaration,
) -> Result<CheckedSourceValueEquation<'a>, SourceValueEquationError> {
    check_source_value_equation(
        module,
        function_id,
        original_environment,
        expected_source,
        proposed,
        SourceProfile::UniformUInt,
    )
}

/// Check a proposed original-source equation at exact mixed Bool/UInt carriers.
/// Bool values remain Bool; UInt values use their actual width's toNat image.
/// The actual module and sorted IR reader determine the complete judgment.
/// This grants no operational, ABI, machine-code or publication permission.
///
/// # Errors
/// Refuses unsupported carriers, calls, different goals, untrusted source
/// declarations, invalid modules and every strict certification failure.
pub fn check_scalar_source_value_equation<'a>(
    module: &'a Module,
    function_id: FuncId,
    original_environment: &'a Environment,
    expected_source: &'a Name,
    proposed: &'a Declaration,
) -> Result<CheckedScalarSourceValueEquation<'a>, SourceValueEquationError> {
    check_source_value_equation(
        module,
        function_id,
        original_environment,
        expected_source,
        proposed,
        SourceProfile::Scalar,
    )
    .map(CheckedScalarSourceValueEquation::new)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum SourceProfile {
    UniformUInt,
    Scalar,
}

#[derive(Clone, Copy)]
enum SourceCarrier {
    Bool,
    UInt(u32),
}

impl SourceCarrier {
    fn from_ir(ty: &Ty) -> Result<Self, SourceValueEquationError> {
        match ty {
            Ty::Bool => Ok(Self::Bool),
            Ty::U8 => Ok(Self::UInt(8)),
            Ty::U16 => Ok(Self::UInt(16)),
            Ty::U32 => Ok(Self::UInt(32)),
            Ty::U64 => Ok(Self::UInt(64)),
            _ => Err(SourceValueEquationError::Unsupported(
                "source-value carrier is not exact Bool/UInt8/16/32/64".into(),
            )),
        }
    }
    fn source_type(self) -> Expr {
        match self {
            Self::Bool => Expr::const_str("Bool"),
            Self::UInt(width) => Expr::const_(Name::from_string(&format!("UInt{width}")), vec![]),
        }
    }
    fn model_sort(self) -> Sort {
        match self {
            Self::Bool => Sort::Bool,
            Self::UInt(width) => Sort::Nat {
                width,
                signed: false,
            },
        }
    }
    fn model_type(self) -> Expr {
        Expr::const_str(match self {
            Self::Bool => "Bool",
            Self::UInt(_) => "Nat",
        })
    }
    fn image(self, value: Expr) -> Expr {
        match self {
            Self::Bool => value,
            Self::UInt(width) => Expr::app(
                Expr::const_(Name::from_string(&format!("UInt{width}.toNat")), vec![]),
                value,
            ),
        }
    }
}

fn check_source_value_equation<'a>(
    module: &'a Module,
    function_id: FuncId,
    original_environment: &'a Environment,
    expected_source: &'a Name,
    proposed: &'a Declaration,
    profile: SourceProfile,
) -> Result<CheckedSourceValueEquation<'a>, SourceValueEquationError> {
    let validation = validate_module_with_config(module, &ValidationConfig::pinned());
    if !validation.is_ok() {
        return Err(SourceValueEquationError::InvalidModule(
            validation.into_errors(),
        ));
    }
    let catalog = ModuleFunctionCatalog::new(module);
    let function = catalog.unique(function_id).ok_or_else(|| {
        SourceValueEquationError::Unsupported("selected function is missing or ambiguous".into())
    })?;
    if function.is_declaration() {
        return Err(SourceValueEquationError::Unsupported(
            "selected function has no body".into(),
        ));
    }
    let signature = module
        .func_types
        .get(function.ty.as_usize())
        .ok_or_else(|| {
            SourceValueEquationError::Unsupported("selected function type is missing".into())
        })?;
    if signature.is_vararg {
        return Err(SourceValueEquationError::Unsupported(
            "vararg source-value signature".into(),
        ));
    }
    let denotation = denote_function_with_catalog(module, &catalog, function)
        .map_err(SourceValueEquationError::Unsupported)?;
    let arity = u32::try_from(denotation.params.len()).map_err(|_| {
        SourceValueEquationError::Unsupported("source-value arity exceeds u32".into())
    })?;
    let (parameters, result) = if profile == SourceProfile::UniformUInt {
        let Sort::Nat {
            width,
            signed: false,
        } = denotation.result
        else {
            return Err(SourceValueEquationError::Unsupported(
                "result is not an unsigned UInt scalar".into(),
            ));
        };
        let exact_result_width = match signature.returns.as_slice() {
            [Ty::U8] => Some(8),
            [Ty::U16] => Some(16),
            [Ty::U32] => Some(32),
            [Ty::U64] => Some(64),
            _ => None,
        };
        if !matches!(width, 8 | 16 | 32 | 64)
            || exact_result_width != Some(width)
            || signature
                .params
                .iter()
                .any(|ty| Some(ty) != signature.returns.first())
            || arity > 64
            || denotation
                .params
                .iter()
                .any(|sort| *sort != denotation.result)
            || !denotation.callees.is_empty()
            || !denotation.callee_ids.is_empty()
            || denotation.body.has_fvar_quick()
            || denotation.body.has_expr_mvar_quick()
            || denotation.body.has_level_mvar_quick()
            || denotation.body.has_level_param_quick()
            || denotation.body.loose_bvar_range() > arity
        {
            return Err(SourceValueEquationError::Unsupported(
                "requires a monomorphic call-free uniform UInt8/16/32/64 denotation with at most 64 parameters".into(),
            ));
        }
        (
            vec![SourceCarrier::UInt(width); denotation.params.len()],
            SourceCarrier::UInt(width),
        )
    } else {
        let [result_type] = signature.returns.as_slice() else {
            return Err(SourceValueEquationError::Unsupported(
                "source-value signature requires exactly one result".into(),
            ));
        };
        let result = SourceCarrier::from_ir(result_type)?;
        let parameters = signature
            .params
            .iter()
            .map(SourceCarrier::from_ir)
            .collect::<Result<Vec<_>, _>>()?;
        if parameters.len() != denotation.params.len()
            || result.model_sort() != denotation.result
            || parameters
                .iter()
                .zip(&denotation.params)
                .any(|(carrier, sort)| carrier.model_sort() != *sort)
            || arity > 64
            || !denotation.callees.is_empty()
            || !denotation.callee_ids.is_empty()
            || denotation.body.has_fvar_quick()
            || denotation.body.has_expr_mvar_quick()
            || denotation.body.has_level_mvar_quick()
            || denotation.body.has_level_param_quick()
            || denotation.body.loose_bvar_range() > arity
        {
            return Err(SourceValueEquationError::Unsupported(
                "requires a closed call-free exact Bool/UInt denotation with at most 64 parameters"
                    .into(),
            ));
        }
        (parameters, result)
    };
    let source = original_environment
        .get_const(expected_source)
        .ok_or_else(|| {
            SourceValueEquationError::Unsupported("expected original source is absent".into())
        })?;
    let expected_signature = parameters
        .iter()
        .rev()
        .fold(result.source_type(), |rest, carrier| {
            Expr::arrow(carrier.source_type(), rest)
        });
    if !matches!(source.kind, ConstantKind::Definition | ConstantKind::Opaque)
        || !source.level_params.is_empty()
        || source.value.is_none()
        || source.type_ != expected_signature
        || original_environment.declaration_verification(expected_source)
            != Some(DeclarationVerification::FullKernelCheck)
    {
        return Err(SourceValueEquationError::Unsupported(
            if profile == SourceProfile::UniformUInt {
                "expected source must be a fully checked monomorphic definition at the exact UInt signature"
            } else {
                "expected source must be a fully checked monomorphic definition at the exact scalar signature"
            }.into(),
        ));
    }

    // The independent reader numbers parameter i as bvar(arity-1-i).
    // Construct the actual-source application in that same telescope. The
    // replacement vector is indexed by the INNERMOST binder, not source order.
    let args = (0..arity).map(|i| Expr::bvar(arity - 1 - i));
    let original_call = Expr::apps(Expr::const_(expected_source.clone(), vec![]), args);
    let lhs = result.image(original_call);
    let nat_images: Vec<_> = parameters
        .iter()
        .rev()
        .enumerate()
        .map(|(i, carrier)| carrier.image(Expr::bvar(i as u32)))
        .collect();
    let rhs = denotation.body.instantiate_rev(&nat_images);
    let mut judgment = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [result.model_type(), lhs, rhs],
    );
    for carrier in parameters.iter().rev() {
        judgment = Expr::pi(BinderInfo::Default, carrier.source_type(), judgment);
    }
    let Declaration::Theorem {
        level_params,
        type_,
        value: proof,
        ..
    } = proposed
    else {
        return Err(SourceValueEquationError::Rejected(
            "witness is not a theorem declaration".into(),
        ));
    };
    if !level_params.is_empty()
        || *type_ != judgment
        || !closed_monomorphic(&judgment)
        || !closed_monomorphic(proof)
    {
        return Err(SourceValueEquationError::Rejected(
            "witness must carry the exact independently re-derived closed monomorphic goal and proof".into(),
        ));
    }
    let audit = original_environment.audit_certification(&judgment, proof);
    if !audit.is_certified() {
        return Err(SourceValueEquationError::Rejected(format!(
            "strict certification audit: {:?}",
            audit.issues
        )));
    }
    // add_decl success alone is not certification in MM/structural import
    // modes. Use a fresh consumer-selected name, then require the exact actual
    // theorem, type, proof and FullKernelCheck before exposing a checked value.
    let name = (0..1024)
        .map(|i| Name::from_string("TrustIrSourceValue.checked").num(i))
        .find(|name| original_environment.get_const(name).is_none())
        .ok_or_else(|| {
            SourceValueEquationError::Rejected("no fresh consumer theorem name".into())
        })?;
    let mut checker = original_environment.clone();
    checker
        .add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: judgment.clone(),
            value: proof.clone(),
        })
        .map_err(|error| {
            SourceValueEquationError::Rejected(format!("kernel admission: {error:?}"))
        })?;
    let admitted = checker.get_const(&name).ok_or_else(|| {
        SourceValueEquationError::Rejected("kernel did not admit the theorem".into())
    })?;
    if admitted.kind != ConstantKind::Theorem
        || admitted.type_ != judgment
        || admitted.value.as_ref() != Some(proof)
        || checker.declaration_verification(&name) != Some(DeclarationVerification::FullKernelCheck)
    {
        return Err(SourceValueEquationError::Rejected(
            "admission did not retain the exact fully checked theorem".into(),
        ));
    }
    let source_closure = original_environment
        .closure_digest(expected_source)
        .map_err(|error| SourceValueEquationError::Rejected(format!("source closure: {error}")))?;
    let equation_closure = checker.closure_digest(&name).map_err(|error| {
        SourceValueEquationError::Rejected(format!("equation closure: {error}"))
    })?;
    Ok(CheckedSourceValueEquation {
        module,
        #[cfg(feature = "source-value-operational")]
        validation,
        function,
        environment: original_environment,
        source: expected_source,
        judgment,
        proof,
        source_closure,
        equation_closure,
    })
}
