// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! A derived, independently replayed connection from one checked source-value
//! equation to the actual ByteV1 machine. No body license, native theorem or
//! source/environment authentication is produced by this component.

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::{
    BinderInfo, ConstantKind, Declaration, DeclarationVerification, Environment, Expr, Level, Name,
    TypeChecker,
};
use trust_ir::{Constant, FuncId, Inst, ValueId};

use crate::CheckedSourceValueEquation;
use crate::core_execution::{
    Assembler, Catalog, Coordinate, Current, EntryTarget, Limits, MachineModel, PendingEquality,
    PendingProof, RootReturnFrame, ScalarPremises,
};
use crate::core_reflection::{
    CoreSignatureDescriptorProfileV1, ReflectedCoreModuleV1,
    reflect_checked_source_runtime_context_v1, reflect_core_module_v1,
    reflect_core_module_with_runtime_signature_descriptors_v1,
};
use crate::scoped_local::{LocalScope, ScopedLocal};

mod arguments;
mod body;
pub mod contextual;
mod execution;

#[derive(Debug)]
pub struct SourceValueOperationalError(pub String);
impl core::fmt::Display for SourceValueOperationalError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.0.fmt(f)
    }
}
impl std::error::Error for SourceValueOperationalError {}
impl From<String> for SourceValueOperationalError {
    fn from(value: String) -> Self {
        Self(value)
    }
}

type Result<T> = core::result::Result<T, String>;

/// Both complete closed claims have passed strict kernel and lossless replay.
/// The exact borrowed source-value pair remains the subject. This is neither a
/// serializable certificate nor permission to emit any function in its module.
pub struct CheckedSourceValueOperational<'a> {
    source: &'a CheckedSourceValueEquation<'a>,
    context: Expr,
    environment: Environment,
    total_claim: Expr,
    total_proof: Expr,
    typed_claim: Expr,
    typed_proof: Expr,
    instruction_count: usize,
    signature_descriptor_profile: CoreSignatureDescriptorProfileV1,
    full_runtime_context: bool,
    // Keep the already-admitted reflection/body plan for contextual consumers.
    // This private data is retained only after both original claims replay.
    subject: Subject<'a>,
}
impl<'a> CheckedSourceValueOperational<'a> {
    /// Reuse exactly the admitted original-module catalog within this crate.
    /// This data borrow is not a new execution or ABI capability.
    pub(crate) fn reflected(&self) -> &ReflectedCoreModuleV1<'a> {
        &self.subject.reflected
    }
    /// Exact original admission retained by the fixed full-runtime-context
    /// caller. This is a borrowed real report, not table bytes or a status flag.
    /// It grants no body license or Rust/native execution refinement.
    pub fn retained_validation_report(&self) -> Option<&crate::ModuleValidationReport<'a>> {
        self.full_runtime_context
            .then(|| self.source.validation_report())
    }
    /// Fixed descriptor interpretation used by this receipt, not ABI authority.
    pub fn signature_descriptor_profile(&self) -> CoreSignatureDescriptorProfileV1 {
        self.signature_descriptor_profile
    }
    pub fn source_value(&self) -> &'a CheckedSourceValueEquation<'a> {
        self.source
    }
    pub fn context(&self) -> &Expr {
        &self.context
    }
    pub fn environment(&self) -> &Environment {
        &self.environment
    }
    pub fn total_claim(&self) -> &Expr {
        &self.total_claim
    }
    pub fn total_proof(&self) -> &Expr {
        &self.total_proof
    }
    pub fn typed_claim(&self) -> &Expr {
        &self.typed_claim
    }
    pub fn typed_proof(&self) -> &Expr {
        &self.typed_proof
    }
    /// Includes the actual final Return; initialization consumes no run fuel.
    pub fn instruction_count(&self) -> usize {
        self.instruction_count
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ScalarProfile {
    U64ConstAdd,
    U32ConstAddMul,
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Arithmetic {
    Add,
    Mul,
}
impl ScalarProfile {
    fn bits(self) -> u64 {
        match self {
            Self::U64ConstAdd => 64,
            Self::U32ConstAddMul => 32,
        }
    }
    fn ty(self) -> trust_ir::Ty {
        match self {
            Self::U64ConstAdd => trust_ir::Ty::U64,
            Self::U32ConstAddMul => trust_ir::Ty::U32,
        }
    }
    fn scalar_type(self) -> Expr {
        app("IRTy.uint_", [nat(self.bits())])
    }
    fn limit(self) -> Expr {
        app("ir_nat_pow2", [nat(self.bits())])
    }
    fn bound(self, value: Expr) -> Expr {
        app("Nat.lt", [value, self.limit()])
    }
    fn maximum(self) -> u64 {
        match self {
            Self::U64ConstAdd => u64::MAX,
            Self::U32ConstAddMul => u32::MAX.into(),
        }
    }
    fn uint_name(self) -> &'static str {
        match self {
            Self::U64ConstAdd => "UInt64",
            Self::U32ConstAddMul => "UInt32",
        }
    }
    fn to_nat(self) -> &'static str {
        match self {
            Self::U64ConstAdd => "UInt64.toNat",
            Self::U32ConstAddMul => "UInt32.toNat",
        }
    }
    fn to_bitvec(self) -> &'static str {
        match self {
            Self::U64ConstAdd => "UInt64.toBitVec",
            Self::U32ConstAddMul => "UInt32.toBitVec",
        }
    }
    fn arithmetic(self, op: trust_ir::BinOp) -> Option<Arithmetic> {
        match op {
            trust_ir::BinOp::Add => Some(Arithmetic::Add),
            trust_ir::BinOp::Mul if self == Self::U32ConstAddMul => Some(Arithmetic::Mul),
            _ => None,
        }
    }
    fn denotation(self, op: Arithmetic, a: Expr, b: Expr) -> Expr {
        let op = match op {
            Arithmetic::Add => "Nat.add",
            Arithmetic::Mul => "Nat.mul",
        };
        app("Nat.mod", [app(op, [a, b]), self.limit()])
    }
    fn actual_word(self, op: Arithmetic, a: Expr, b: Expr) -> Expr {
        if self == Self::U64ConstAdd && op == Arithmetic::Add {
            return fast(a, b);
        }
        let op = match op {
            Arithmetic::Add => "Nat.add",
            Arithmetic::Mul => "ir_nat_mul",
        };
        app("ir_wrap", [nat(self.bits()), app(op, [a, b])])
    }
    fn profile_error(self) -> &'static str {
        match self {
            Self::U64ConstAdd => {
                "operational source-value profile requires exactly (U64,U64)->U64 in one block"
            }
            Self::U32ConstAddMul => {
                "operational source-value profile requires exactly (U32,U32)->U32 in one block"
            }
        }
    }
    fn operation_error(self) -> &'static str {
        match self {
            Self::U64ConstAdd => {
                "operational source-value supports only actual U64 Const/Add and final Return"
            }
            Self::U32ConstAddMul => {
                "operational source-value supports only actual U32 Const/Add/Mul and final Return"
            }
        }
    }
}

#[derive(Clone)]
enum Operation {
    Constant {
        destination: ValueId,
        literal: u64,
    },
    Arithmetic {
        kind: Arithmetic,
        destination: ValueId,
        left: ValueId,
        right: ValueId,
    },
}
struct Subject<'a> {
    source: &'a CheckedSourceValueEquation<'a>,
    profile: ScalarProfile,
    reflected: ReflectedCoreModuleV1<'a>,
    parameters: [ValueId; 2],
    operations: Vec<Operation>,
    returned: ValueId,
    limits: Limits,
}

fn c(name: &str) -> Expr {
    if name == "Eq.refl" {
        Expr::const_(Name::from_string(name), vec![Level::succ(Level::zero())])
    } else {
        Expr::const_str(name)
    }
}
fn app(name: &str, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), arguments)
}
fn nat(value: u64) -> Expr {
    Expr::nat_lit(value)
}
fn eq(ty: Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, left, right],
    )
}
fn list(ty: &str, values: impl IntoIterator<Item = Expr>) -> Expr {
    let values: Vec<_> = values.into_iter().collect();
    values
        .into_iter()
        .rev()
        .fold(app("IRList.nil", [c(ty)]), |tail, head| {
            app("IRList.cons", [c(ty), head, tail])
        })
}
fn choose(ty: Expr, flag: Expr, yes: Expr, no: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::lam(BinderInfo::Default, c("Bool"), ty), no, yes, flag],
    )
}
fn int(value: Expr) -> Expr {
    app("IRScalar.int_", [value])
}
fn limit() -> Expr {
    app("ir_nat_pow2", [nat(64)])
}
fn fast(a: Expr, b: Expr) -> Expr {
    let sum = app("Nat.add", [a, b]);
    choose(
        c("Nat"),
        app("ir_nat_ltb", [sum.clone(), limit()]),
        sum.clone(),
        app("Nat.sub", [sum, limit()]),
    )
}
fn den_add(a: Expr, b: Expr) -> Expr {
    app("Nat.mod", [app("Nat.add", [a, b]), limit()])
}
fn close(scope: &LocalScope, parameters: &[ScopedLocal], body: Expr, proof: bool) -> Result<Expr> {
    scope
        .close(&parameters.iter().rev().fold(body, |body, local| {
            if proof {
                local.lam(body)
            } else {
                local.pi(body)
            }
        }))
        .map_err(|e| e.to_string())
}
fn pending(ty: Expr, value: Expr) -> PendingEquality {
    PendingEquality::reflexive(ty, value)
}
fn truth(assembler: &mut Assembler<'_>, expression: Expr) -> Result<PendingEquality> {
    assembler.conversion(c("Bool"), expression, c("Bool.true"))
}
fn symm(equality: &PendingEquality) -> PendingEquality {
    let ty = equality.proposition().get_app_args()[0].clone();
    PendingEquality::candidate(
        ty.clone(),
        equality.right().clone(),
        equality.left().clone(),
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.symm"),
                vec![Level::succ(Level::zero())],
            ),
            [
                ty,
                equality.left().clone(),
                equality.right().clone(),
                equality.term().clone(),
            ],
        ),
    )
}

fn mapped(
    assembler: &mut Assembler<'_>,
    equality: PendingEquality,
    ty: Expr,
    map: impl Fn(Expr) -> Expr,
) -> Result<PendingEquality> {
    let left = map(equality.left().clone());
    let right = map(equality.right().clone());
    let proof = assembler.congruence(equality, ty, map)?;
    assembler.convert_endpoints(proof, left, right)
}

impl<'a> Subject<'a> {
    fn new(
        source: &'a CheckedSourceValueEquation<'a>,
        addresses: &[(FuncId, u64)],
        limits: Limits,
        profile: ScalarProfile,
        signature_descriptor_profile: CoreSignatureDescriptorProfileV1,
        full_runtime_context: bool,
    ) -> Result<Self> {
        // The complete actual module is reflected. A generated helper cannot be
        // dropped or replaced with a conveniently authored selected module.
        let reflected = if full_runtime_context {
            reflect_checked_source_runtime_context_v1(source, addresses)
        } else {
            match signature_descriptor_profile {
                CoreSignatureDescriptorProfileV1::StrictValuesV1 => {
                    reflect_core_module_v1(source.module(), addresses)
                }
                CoreSignatureDescriptorProfileV1::RuntimeDeclarationsV1 => {
                    reflect_core_module_with_runtime_signature_descriptors_v1(
                        source.module(),
                        addresses,
                    )
                }
            }
        }
        .map_err(|e| e.to_string())?;
        let function = source.function();
        let signature = &source.module().func_types[function.ty.as_usize()];
        if signature.params != [profile.ty(), profile.ty()]
            || signature.returns != [profile.ty()]
            || signature.is_vararg
            || function.blocks.len() != 1
        {
            return Err(profile.profile_error().into());
        }
        let block = &function.blocks[0];
        if block.id != function.entry || block.params.len() != 2 {
            return Err("operational source-value entry parameters".into());
        }
        let parameters = [block.params[0].0, block.params[1].0];
        let (terminal, prefix) = block.body.split_last().ok_or("empty source-value body")?;
        let Inst::Return { values } = &terminal.inst else {
            return Err("operational source-value requires final Return".into());
        };
        let [returned] = values.as_slice() else {
            return Err("operational source-value requires one returned SSA value".into());
        };
        let mut operations = Vec::new();
        let mut available: BTreeSet<_> = parameters.into_iter().collect();
        for node in prefix {
            let [destination] = node.results.as_slice() else {
                return Err(
                    "operational scalar instruction requires exactly one actual destination".into(),
                );
            };
            if available.contains(destination) {
                return Err("operational SSA destination reused".into());
            }
            let operation = match &node.inst {
                Inst::Const {
                    ty,
                    value: Constant::Int(value),
                } if *ty == profile.ty()
                    && *value >= 0
                    && *value <= i128::from(profile.maximum()) =>
                {
                    Operation::Constant {
                        destination: *destination,
                        literal: *value as u64,
                    }
                }
                Inst::BinOp { op, ty, lhs, rhs }
                    if *ty == profile.ty()
                        && profile.arithmetic(*op).is_some()
                        && available.contains(lhs)
                        && available.contains(rhs) =>
                {
                    Operation::Arithmetic {
                        kind: profile.arithmetic(*op).unwrap(),
                        destination: *destination,
                        left: *lhs,
                        right: *rhs,
                    }
                }
                _ => return Err(profile.operation_error().into()),
            };
            operations.push(operation);
            available.insert(*destination);
        }
        if !available.contains(returned) {
            return Err("returned SSA value is unavailable".into());
        }
        Ok(Self {
            source,
            profile,
            reflected,
            parameters,
            operations,
            returned: *returned,
            limits,
        })
    }
    fn denotation(&self, x: Expr, y: Expr) -> Expr {
        let mut values = BTreeMap::from([(self.parameters[0], x), (self.parameters[1], y)]);
        for operation in &self.operations {
            let (id, value) = match operation {
                Operation::Constant {
                    destination,
                    literal,
                } => (*destination, nat(*literal)),
                Operation::Arithmetic {
                    kind,
                    destination,
                    left,
                    right,
                } => (
                    *destination,
                    self.profile
                        .denotation(*kind, values[left].clone(), values[right].clone()),
                ),
            };
            values.insert(id, value);
        }
        values[&self.returned].clone()
    }
}

fn extended_environment(source: &CheckedSourceValueEquation<'_>) -> Result<Environment> {
    // Reuse the pinned checked canonical arithmetic and its existing Nat.mod
    // bridge. This also retains the ordinary C/Fast ByteV1 initializer.
    let mut environment = clean_verify::source_ir_word64_addition::environment()?;
    import_source_closure(&mut environment, source.environment(), source)?;
    if environment
        .closure_digest(source.source())
        .map_err(|e| e.to_string())?
        != *source.source_closure_digest()
    {
        return Err("original source closure changed in operational environment".into());
    }
    Ok(environment)
}

pub(crate) fn import_source_closure(
    destination: &mut Environment,
    original: &Environment,
    source: &CheckedSourceValueEquation<'_>,
) -> Result<()> {
    let mut names: BTreeSet<_> = original
        .dependency_closure(source.source())
        .map_err(|e| e.to_string())?
        .into_iter()
        .collect();
    let mut proof_reads = std::collections::HashSet::new();
    source.proof().collect_kernel_reads_into(&mut proof_reads);
    for root in proof_reads {
        names.extend(
            original
                .dependency_closure(&root)
                .map_err(|e| e.to_string())?,
        );
    }
    import_checked_declarations(destination, original, names)?;
    // Reconstruct the ORIGINAL consumer-selected theorem identity, including
    // proof-only projection/inductive metadata dependencies in its full digest.
    let name = (0..1024)
        .map(|i| Name::from_string("TrustIrSourceValue.checked").num(i))
        .find(|name| original.get_const(name).is_none())
        .ok_or("no original consumer theorem name")?;
    if destination.get_const(&name).is_some() {
        return Err("consumer theorem name collides in operational environment".into());
    }
    strict_replay(destination, source.judgment(), source.proof())?;
    destination
        .add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: source.judgment().clone(),
            value: source.proof().clone(),
        })
        .map_err(|e| format!("source theorem re-admission: {e:?}"))?;
    if destination.declaration_verification(&name) != Some(DeclarationVerification::FullKernelCheck)
        || destination
            .closure_digest(&name)
            .map_err(|e| e.to_string())?
            != *source.equation_closure_digest()
    {
        return Err("original equation closure changed in operational environment".into());
    }
    Ok(())
}

/// Admit an original checked dependency closure without changing its meaning.
/// Existing constants must have exactly equal declaration info; new axioms,
/// missing bodies and unchecked declarations remain refused. Callers retain
/// their own rooted closure-digest and final theorem checks.
pub(crate) fn import_checked_declarations(
    destination: &mut Environment,
    original: &Environment,
    mut names: BTreeSet<Name>,
) -> Result<()> {
    while !names.is_empty() {
        let mut progress = false;
        let mut remaining = BTreeSet::new();
        for name in names {
            let info = original
                .get_const(&name)
                .ok_or("missing original source declaration")?;
            if let Some(existing) = destination.get_const(&name) {
                if existing != info {
                    return Err(format!("original source/environment collision: {name}"));
                }
                progress = true;
                continue;
            }
            let mut dependencies = info.type_.collect_constants();
            if let Some(value) = &info.value {
                dependencies.extend(value.collect_constants());
            }
            if dependencies
                .iter()
                .any(|dependency| destination.get_const(dependency).is_none())
            {
                remaining.insert(name);
                continue;
            }
            if original.declaration_verification(&name)
                != Some(DeclarationVerification::FullKernelCheck)
            {
                return Err(format!(
                    "original declaration was not fully checked: {name}"
                ));
            }
            let value = info
                .value
                .clone()
                .ok_or("source closure contains a new axiom or unavailable body")?;
            let declaration = match info.kind {
                ConstantKind::Definition => Declaration::Definition {
                    name: name.clone(),
                    level_params: info.level_params.clone(),
                    type_: info.type_.clone(),
                    value,
                    is_reducible: info.is_reducible,
                },
                ConstantKind::Opaque => Declaration::Opaque {
                    name: name.clone(),
                    level_params: info.level_params.clone(),
                    type_: info.type_.clone(),
                    value,
                },
                ConstantKind::Theorem => Declaration::Theorem {
                    name: name.clone(),
                    level_params: info.level_params.clone(),
                    type_: info.type_.clone(),
                    value,
                },
                ConstantKind::Axiom => return Err("new source axiom is unsupported".into()),
            };
            destination
                .add_decl(declaration)
                .map_err(|e| format!("source re-admission {name}: {e:?}"))?;
            if destination.get_const(&name) != Some(info)
                || destination.declaration_verification(&name)
                    != Some(DeclarationVerification::FullKernelCheck)
            {
                return Err(format!("source re-admission changed declaration: {name}"));
            }
            progress = true;
        }
        if !progress {
            return Err("source closure requires unsupported inductive/import metadata".into());
        }
        names = remaining;
    }
    Ok(())
}

pub(crate) fn strict_replay(environment: &Environment, claim: &Expr, proof: &Expr) -> Result<()> {
    let closed = |term: &Expr| {
        !term.has_fvar_quick()
            && !term.has_loose_bvars()
            && !term.has_expr_mvar_quick()
            && !term.has_level_mvar_quick()
            && !term.has_level_param_quick()
    };
    if !closed(claim) || !closed(proof) {
        return Err("open or metavariable operational source-value claim".into());
    }
    let check = |proof: &Expr| -> Result<()> {
        let mut checker = TypeChecker::new(environment);
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        let checked_claim = checker.check_type(claim, &Expr::sort(Level::zero()));
        if checker.heartbeat_spent() || clean_kernel::tc::declaration_budget_exhausted() {
            return Err("operational resource stop is not a verdict".into());
        }
        checked_claim.map_err(|_| "operational claim failed strict kernel checking".to_owned())?;
        let checked = checker.check_type(proof, claim);
        if checker.heartbeat_spent() || clean_kernel::tc::declaration_budget_exhausted() {
            return Err("operational resource stop is not a verdict".into());
        }
        checked.map_err(|_| "operational proof failed strict kernel checking".to_owned())?;
        let audit = environment.audit_certification(claim, proof);
        if !audit.is_certified() {
            return Err(format!("operational audit: {audit:?}"));
        }
        for name in audit.dependencies {
            for dependencies in [
                environment.axiom_deps(&name),
                environment.foundational_axiom_deps(&name),
                environment.trust_marker_deps(&name),
            ] {
                if !dependencies
                    .ok_or("missing operational dependency closure")?
                    .is_empty()
                {
                    return Err("axiom or trust marker in operational claim".into());
                }
            }
        }
        Ok(())
    };
    check(proof)?;
    let bytes = trust_ir::proof::encode_clean_expr_dag_v2(proof)
        .map_err(|e| format!("operational encode: {e:?}"))?;
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&bytes)
        .map_err(|e| format!("operational decode: {e:?}"))?;
    if decoded != *proof {
        return Err("operational lossless replay changed proof".into());
    }
    check(&decoded)
}

/// Check total arbitrary-argument execution and the connected typed source.
///
/// The complete actual module must pass the canonical little-endian 64-bit
/// C/Fast reflector. The selected function has exactly two U64 parameters, one
/// U64 result and one block of U64 Const/Add instructions followed by Return.
/// Copy, calls, branches and unsupported full-module metadata are refused. In
/// particular no generated helper is removed to make a module fit this profile.
///
/// Both closed claims quantify a host type `W : Type`, memory, host value,
/// arbitrary providers and every fuel. The total claim also quantifies every
/// `IRList IRScalar` argument list: initial-memory failure precedes arity and
/// carrier failure. Short fuel retains the exact running prefix; fuel beyond
/// Return retains the halted result. The typed claim quantifies two UInt64
/// values and connects the result to the SAME original source declaration.
/// Root retirement, the empty owner stack and updated next-owner field are
/// retained; no unchanged whole-world or physical calling-convention claim is
/// made. This is Clean's ByteV1 model, not the separate W5b Lean evaluator.
///
/// One construction ledger is shared by both candidates. Lookup candidate and
/// cache limits apply per catalog; heartbeat caps apply per lookup. These are
/// not a total CPU, replay or allocation bound. Every candidate must
/// pass strict rooted kernel audit and lossless DAG replay before this separate
/// receipt is returned. Existing body licenses and the source-value receipt are
/// unchanged. Source-text/environment provenance, reflection/layout fidelity,
/// native correctness and SourceNoUB remain external obligations.
pub fn check_u64_straight_line_source_value<'a>(
    source: &'a CheckedSourceValueEquation<'a>,
    addresses: &[(FuncId, u64)],
    limits: Limits,
) -> core::result::Result<CheckedSourceValueOperational<'a>, SourceValueOperationalError> {
    check_profile(
        source,
        addresses,
        limits,
        ScalarProfile::U64ConstAdd,
        CoreSignatureDescriptorProfileV1::StrictValuesV1,
        false,
    )
}

/// Check a two-UInt32 source against its exact U32 Const/Add/Mul/Return body.
///
/// Both the total arbitrary-raw-argument and typed UInt32 claims are derived
/// with one construction ledger. Each complete closed proof then passes strict
/// rooted kernel checking and lossless replay. The scalar profile is 32; the
/// complete module, machine, pointers, memory and owners retain the canonical
/// little-endian 64-bit C/Fast model. Negative or oversized
/// constants, unsupported operations/metadata and generated helpers are not
/// rewritten, truncated, removed or licensed. Raw out-of-range arguments fail
/// admission; the pure all-Nat arithmetic helpers do not relax that guard.
/// Error priority, all fuel prefixes, root retirement, source/environment
/// closure binding and the U64 factory's authority limits are unchanged.
/// This default-off API grants no native, provenance or body-license theorem.
pub fn check_u32_straight_line_source_value<'a>(
    source: &'a CheckedSourceValueEquation<'a>,
    addresses: &[(FuncId, u64)],
    limits: Limits,
) -> core::result::Result<CheckedSourceValueOperational<'a>, SourceValueOperationalError> {
    check_profile(
        source,
        addresses,
        limits,
        ScalarProfile::U32ConstAddMul,
        CoreSignatureDescriptorProfileV1::StrictValuesV1,
        false,
    )
}

/// Check the same fixed U32 source connection while retaining unused runtime
/// signature descriptors. The selected body and all total/typed proof, source
/// closure, strict-audit and lossless-replay obligations are unchanged.
/// Float/variadic declarations remain present, but no successful activation,
/// provider fidelity, native ABI or body license is established. The complete
/// actual Clean fixture still fails its metadata/Release boundaries.
pub fn check_u32_straight_line_source_value_with_runtime_signature_descriptors<'a>(
    source: &'a CheckedSourceValueEquation<'a>,
    addresses: &[(FuncId, u64)],
    limits: Limits,
) -> core::result::Result<CheckedSourceValueOperational<'a>, SourceValueOperationalError> {
    check_profile(
        source,
        addresses,
        limits,
        ScalarProfile::U32ConstAddMul,
        CoreSignatureDescriptorProfileV1::RuntimeDeclarationsV1,
        false,
    )
}

/// Check the selected call-free two-U32 Const/Add/Mul/Return source in its
/// complete, originally validated runtime module. The exact successful pinned
/// SourceEq report and both proof tables remain borrowed from that SAME source
/// object; no table-cleared clone or caller-selected context is accepted.
/// All19 Function fields, signatures, layouts and sites stay original. Runtime
/// float/vararg descriptors are retained. Release syntax is preserved exactly
/// but its canonical step remains explicitly unmodelled, never ARC success.
///
/// Both total/typed claims use the existing construction ledger, strict rooted
/// no-axiom/trust-marker audit and lossless replay. The Rust reflection/layout
/// boundary remains TCB. This is neither Rust host-metadata noninterference nor
/// native ABI, provider fidelity, NoUB or a helper body license.
pub fn check_u32_straight_line_source_value_with_validated_runtime_context<'a>(
    source: &'a CheckedSourceValueEquation<'a>,
    addresses: &[(FuncId, u64)],
    limits: Limits,
) -> core::result::Result<CheckedSourceValueOperational<'a>, SourceValueOperationalError> {
    check_profile(
        source,
        addresses,
        limits,
        ScalarProfile::U32ConstAddMul,
        CoreSignatureDescriptorProfileV1::RuntimeDeclarationsV1,
        true,
    )
}

fn check_profile<'a>(
    source: &'a CheckedSourceValueEquation<'a>,
    addresses: &[(FuncId, u64)],
    limits: Limits,
    profile: ScalarProfile,
    signature_descriptor_profile: CoreSignatureDescriptorProfileV1,
    full_runtime_context: bool,
) -> core::result::Result<CheckedSourceValueOperational<'a>, SourceValueOperationalError> {
    let subject = Subject::new(
        source,
        addresses,
        limits,
        profile,
        signature_descriptor_profile,
        full_runtime_context,
    )?;
    let environment = extended_environment(source)?;
    if full_runtime_context {
        // The exact canonical owner/telescopes must be the Release33 epoch;
        // an equal execution-label string or invented constructor is not enough.
        clean_verify::eval_ir::checked_syntax_identity(
            &environment,
            clean_verify::eval_ir::EvalIrSyntaxEpoch::RetainedRelease,
        )
        .map_err(|e| format!("full runtime context requires canonical Release33: {e}"))?;
    }
    let (total_claim, total_proof, typed_claim, typed_proof) =
        arguments::derive(&subject, &environment)?;
    strict_replay(&environment, &total_claim, &total_proof)?;
    strict_replay(&environment, &typed_claim, &typed_proof)?;
    Ok(CheckedSourceValueOperational {
        source,
        context: subject.reflected.context_term().clone(),
        environment,
        total_claim,
        total_proof,
        typed_claim,
        typed_proof,
        instruction_count: subject.operations.len() + 1,
        signature_descriptor_profile,
        full_runtime_context,
        subject,
    })
}
