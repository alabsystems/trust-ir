// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Level S, checked (amendment S, `docs/SPEC_RATIFICATIONS.md` §22):
//! [`validate_template`] (T1–T9) and [`instantiate`], the pure, checked
//! function from a template and a host's answers to a level-R module.
//!
//! The carrier, its codecs and its structural rules are
//! [`trust_ir::template`]'s. This module adds what needs the level-R
//! validator: T6, which runs `validate_module` over the template's SKOLEM
//! instance (every parameter and opaque hole a fresh layout-less struct, every
//! structured hole a fresh row with exactly its contract), and
//! instantiation's postcondition.
//!
//! What the host is trusted for, and only that: its answers mean what the
//! source means at the instance (Trust's TEMPLATE-HOST row, owner ruling
//! D39). Everything else is checked here: every answer against its contract,
//! the host's edits as append-only, the drop rewrite, and the output against
//! every level-R rule.

use std::collections::{BTreeMap, BTreeSet};

pub use trust_ir::template::{
    Destructor, GlobalAnswer, HoleAnswer, InstArg, InstanceHeader, LinkAnswer, ScriptedAnswer,
    ScriptedHost, TupleLayout,
};
use trust_ir::template::{
    GenericRows, HoleDef, HoleKind, HostKey, TEMPLATE_HOLE_ROW_PREFIX,
    TEMPLATE_INSTANCE_DIGEST_DOMAIN, Template, TemplateArg, TemplateError, TemplateParam,
    TypeContract, is_template_scalar,
};
use trust_ir::{
    BlockId, BodyGate, CallingConv, Constant, ConstantG, EnumDef, FuncAttrs, FuncId, FuncTy,
    FuncTyId, Function, FunctionG, Global, HoleId, Inst, InstG, Linkage, Module, ProofDigest,
    StructDef, StructRepr, TemplateRef, Ty, TyG, TyId, Visibility,
};

mod retained;
pub use retained::{RetainedInstantiation, instantiate_retained};

use crate::validate::{ValidationError, validate_module};

// ---------------------------------------------------------------------------
// Validation (T1–T9)
// ---------------------------------------------------------------------------

/// A refusal of a template by `validate_template`: a structural rule (T1–T5,
/// T7–T9, [`TemplateError`]) or a level-R rule its skolem instance breaks
/// (T6).
#[derive(Debug, Clone, PartialEq)]
pub enum TemplateViolation {
    /// A structural rule.
    Structure(TemplateError),
    /// T6: a level-R rule the template's skolem instance breaks.
    LevelR(ValidationError),
}

impl core::fmt::Display for TemplateViolation {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            TemplateViolation::Structure(error) => write!(f, "{error}"),
            TemplateViolation::LevelR(error) => write!(f, "T6: the skolem instance: {error}"),
        }
    }
}

/// Every violation of T1–T9, structural rules first. T6 runs only on a
/// structurally valid template (its skolem instance needs one).
#[must_use]
pub fn validate_template(template: &Template) -> Vec<TemplateViolation> {
    let structural = template.structural_violations();
    if !structural.is_empty() {
        return structural
            .into_iter()
            .map(TemplateViolation::Structure)
            .collect();
    }
    match skolem_instance(template) {
        Ok(module) => validate_module(&module)
            .into_iter()
            .map(TemplateViolation::LevelR)
            .collect(),
        // The skolem host answers every question by construction, so a
        // structurally valid template always has a skolem instance; should
        // one not, the template is refused by name rather than admitted.
        Err(error) => vec![TemplateViolation::Structure(
            TemplateError::TemplateUnsupported {
                what: format!("a template with no skolem instance ({error})"),
            },
        )],
    }
}

/// The template's skolem instance (T6): instantiation's steps 2–7 run by the
/// internal skolem host, with every parameter-dependent drop left in place
/// (unresolved, which `validate_module` admits) and no tuple-layout question.
pub fn skolem_instance(template: &Template) -> Result<Module, InstantiateError> {
    let mut host = SkolemHost::new(template);
    let (module, _, _) = run(template, &mut host, Mode::Skolem)?;
    Ok(module)
}

// ---------------------------------------------------------------------------
// The host interface
// ---------------------------------------------------------------------------

/// A host's refusal to answer, with its reason.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HostRefusal(pub String);

/// The facts a template leaves to its consumer, asked in a fixed order
/// (arguments; type and const holes by id; callee and global holes by id;
/// the instance header; destructors; tuple layouts). Every method may APPEND
/// rows to `cx`, the instance under construction (it starts with the
/// template's ground rows, at their ids), and answers in its ids. Nothing
/// that existed before a call may change: `instantiate` checks it after every
/// call (`HostRowsInvalid`). Every answer is checked; what the format cannot
/// check is that an answer means what the source means — the host's claim.
pub trait InstantiationHost {
    fn arguments(
        &mut self,
        cx: &mut Module,
        params: &[TemplateParam],
    ) -> Result<Vec<InstArg>, HostRefusal>;
    fn type_hole(
        &mut self,
        cx: &mut Module,
        hole: HoleId,
        key: &HostKey,
        args: &[InstArg],
    ) -> Result<Ty, HostRefusal>;
    fn const_hole(
        &mut self,
        cx: &mut Module,
        hole: HoleId,
        key: &HostKey,
        args: &[InstArg],
        ty: &Ty,
    ) -> Result<Constant, HostRefusal>;
    fn callee_hole(
        &mut self,
        cx: &mut Module,
        hole: HoleId,
        key: &HostKey,
        args: &[InstArg],
        sig: &FuncTy,
    ) -> Result<LinkAnswer, HostRefusal>;
    fn global_hole(
        &mut self,
        cx: &mut Module,
        hole: HoleId,
        key: &HostKey,
        args: &[InstArg],
        ty: &Ty,
        mutable: bool,
    ) -> Result<GlobalAnswer, HostRefusal>;
    fn instance(&mut self, cx: &mut Module, sig: &FuncTy) -> Result<InstanceHeader, HostRefusal>;
    fn destructor(&mut self, cx: &mut Module, ty: &Ty) -> Result<Destructor, HostRefusal>;
    fn tuple_layout(
        &mut self,
        cx: &mut Module,
        ty: &Ty,
    ) -> Result<Option<TupleLayout>, HostRefusal>;
}

/// Which host question an error names.
#[derive(Debug, Clone, PartialEq)]
pub enum Question {
    Arguments,
    Hole(HoleId),
    Instance,
    Destructor(Ty),
    TupleLayout(Ty),
}

impl core::fmt::Display for Question {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Question::Arguments => f.write_str("the arguments"),
            Question::Hole(hole) => write!(f, "hole ?{}", hole.index()),
            Question::Instance => f.write_str("the instance header"),
            Question::Destructor(ty) => write!(f, "the destructor of {ty}"),
            Question::TupleLayout(ty) => write!(f, "the layout of {ty}"),
        }
    }
}

/// A refusal of an instantiation. Each variant is a rule of §5 and has a
/// must-refuse row; nothing is returned with any of them.
#[derive(Debug, Clone, PartialEq)]
pub enum InstantiateError {
    /// Step 1: the template breaks T1–T9.
    TemplateInvalid(Vec<TemplateViolation>),
    /// Step 3: the host gave a different number of arguments than parameters.
    ArityMismatch { expected: usize, got: usize },
    /// Step 3: an argument of the wrong kind for its parameter.
    ArgumentKind { param: u32, why: String },
    /// A host refused a question.
    HostRefused { question: Question, why: String },
    /// A host call changed something that existed before it.
    HostRowsInvalid { question: Question, why: String },
    /// An answer that breaks its hole's contract.
    AnswerContract { hole: u32, why: String },
    /// Two answers that cannot both hold (one symbol, two signatures; one
    /// glue, two types), or an answer the instance has no id left to record
    /// (a full module table: refused, never a panic).
    AnswerConflict { why: String },
    /// The instance header does not fit the body.
    InstanceHeader { why: String },
    /// Step 10: the output breaks a level-R rule; nothing is returned.
    OutputInvalid(Vec<ValidationError>),
}

impl core::fmt::Display for InstantiateError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            InstantiateError::TemplateInvalid(violations) => {
                write!(f, "the template is invalid:")?;
                for violation in violations {
                    write!(f, " {violation};")?;
                }
                Ok(())
            }
            InstantiateError::ArityMismatch { expected, got } => {
                write!(f, "{got} arguments for {expected} parameters")
            }
            InstantiateError::ArgumentKind { param, why } => {
                write!(f, "argument ${param}: {why}")
            }
            InstantiateError::HostRefused { question, why } => {
                write!(f, "the host refused {question}: {why}")
            }
            InstantiateError::HostRowsInvalid { question, why } => {
                write!(
                    f,
                    "answering {question}, the host changed the instance: {why}"
                )
            }
            InstantiateError::AnswerContract { hole, why } => {
                write!(f, "the answer to ?{hole} breaks its contract: {why}")
            }
            InstantiateError::AnswerConflict { why } => write!(f, "conflicting answers: {why}"),
            InstantiateError::InstanceHeader { why } => write!(f, "instance header: {why}"),
            InstantiateError::OutputInvalid(errors) => {
                write!(f, "the instance breaks level R:")?;
                for error in errors {
                    write!(f, " {error};")?;
                }
                Ok(())
            }
        }
    }
}

impl std::error::Error for InstantiateError {}

/// Every question asked and its answer, in order (diagnostic; the output is
/// a function of these and the template).
#[derive(Debug, Clone, PartialEq, Default)]
pub struct AnswerLog {
    pub arguments: Vec<InstArg>,
    pub holes: Vec<(HoleId, HoleAnswer)>,
    pub header: Option<InstanceHeader>,
    pub destructors: Vec<(Ty, Destructor)>,
    pub tuple_layouts: Vec<(Ty, Option<TupleLayout>)>,
}

/// A checked instance.
#[derive(Debug, Clone, PartialEq)]
pub struct Instantiated {
    /// Level R, self-contained: the body, its declarations and its rows;
    /// `validate_module` accepts it.
    pub module: Module,
    /// The template's `trust_ir.template.v1` digest.
    pub template_digest: ProofDigest,
    /// `trust_ir.template.instance.v1` over (template digest, the output's
    /// `stable_digest`): the instance's identity (S12, review R5).
    pub instance_digest: ProofDigest,
    pub answers: AnswerLog,
}

/// Instantiate `template` with `host`'s answers (amendment S, §5). Pure: the
/// output is a function of the template and the answers (the rows the host
/// appended included). Returns only an output `validate_module` accepts.
pub fn instantiate(
    template: &Template,
    host: &mut dyn InstantiationHost,
) -> Result<Instantiated, InstantiateError> {
    instantiate_mapped(template, host).map(|(instance, _)| instance)
}

fn instantiate_mapped(
    template: &Template,
    host: &mut dyn InstantiationHost,
) -> Result<(Instantiated, BTreeMap<FuncId, FuncId>), InstantiateError> {
    let violations = validate_template(template);
    if !violations.is_empty() {
        return Err(InstantiateError::TemplateInvalid(violations));
    }
    let (module, answers, functions) = run(template, host, Mode::Real)?;
    let errors = validate_module(&module);
    if !errors.is_empty() {
        return Err(InstantiateError::OutputInvalid(errors));
    }
    // The instance identity hashes the output's `stable_digest`; a valid
    // module can still have no wire image (a construct ahead of its carrier,
    // a count past the format), so the writer's check walk refuses it by name
    // first (`docs/SPEC_RATIFICATIONS.md`, "A construct or count with no wire
    // image is refused by the writer's own arm, at every trust-ir entry
    // point").
    if let Some(blocker) = crate::wire_identity_blocker(&module) {
        return Err(InstantiateError::OutputInvalid(vec![blocker]));
    }
    let template_digest = template.digest().map_err(|error| {
        InstantiateError::TemplateInvalid(vec![TemplateViolation::Structure(error)])
    })?;
    let instance_digest = instance_digest(&template_digest, &module);
    Ok((
        Instantiated {
            module,
            template_digest,
            instance_digest,
            answers,
        },
        functions,
    ))
}

/// `trust_ir.template.instance.v1` over (template digest, output digest).
#[must_use]
pub fn instance_digest(template_digest: &ProofDigest, module: &Module) -> ProofDigest {
    let mut preimage = Vec::with_capacity(64);
    preimage.extend_from_slice(&template_digest.bytes);
    preimage.extend_from_slice(&module.stable_digest().bytes);
    ProofDigest::sha256_domain(TEMPLATE_INSTANCE_DIGEST_DOMAIN, &preimage)
}

// ---------------------------------------------------------------------------
// The algorithm
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    /// A consumer's instantiation: every step.
    Real,
    /// T6's skolem instance: no destructor or tuple-layout question, and
    /// parameter-dependent drops left in place.
    Skolem,
}

/// The reserved name a placeholder row carries while the host answers: never
/// a link symbol, never matched by an interner (its type is `Ty::Error`).
const RESERVED_PREFIX: &str = "!template_reserved::";

/// The skolem instance's body symbol: a plain name, so the level-R rules
/// judge the body exactly as they would an instance's.
const SKOLEM_BODY_SYMBOL: &str = "__skolem_instance";

struct Sigma<'t> {
    template: &'t Template,
    args: Vec<InstArg>,
    answers: Vec<Option<HoleAnswer>>,
}

impl Sigma<'_> {
    fn ext_ty(&self, r: &TemplateRef) -> Result<Ty, String> {
        match r {
            TemplateRef::Param(p) => match self.args.get(p.as_usize()) {
                Some(InstArg::Type(ty)) => Ok(ty.clone()),
                _ => Err(format!("${} is not a type argument", p.index())),
            },
            TemplateRef::Hole(h) => match self.answers.get(h.as_usize()) {
                Some(Some(HoleAnswer::Type(ty))) => Ok(ty.clone()),
                _ => Err(format!("?{} has no type answer yet", h.index())),
            },
        }
    }

    fn ty(&self, ty: &TyG<TemplateRef>) -> Result<Ty, String> {
        ty.try_map_ext(&mut |r| self.ext_ty(r))
    }

    fn constant(&self, c: &ConstantG<TemplateRef>) -> Result<Constant, String> {
        c.try_map_ext(&mut |r| match r {
            TemplateRef::Param(p) => match self.args.get(p.as_usize()) {
                Some(InstArg::Const(c)) => Ok(c.clone()),
                _ => Err(format!("${} is not a const argument", p.index())),
            },
            TemplateRef::Hole(h) => match self.answers.get(h.as_usize()) {
                Some(Some(HoleAnswer::Const(c))) => Ok(c.clone()),
                _ => Err(format!("?{} has no const answer yet", h.index())),
            },
        })
    }

    fn arg(&self, arg: &TemplateArg) -> Result<InstArg, String> {
        Ok(match arg {
            TemplateArg::Type(ty) => InstArg::Type(self.ty(ty)?),
            TemplateArg::Const { value, .. } => InstArg::Const(self.constant(value)?),
            TemplateArg::Host(p) => match self.args.get(p.as_usize()) {
                Some(InstArg::Host(key)) => InstArg::Host(key.clone()),
                _ => return Err(format!("${} is not a host argument", p.index())),
            },
        })
    }

    fn hole(&self, h: usize) -> &HoleDef {
        &self.template.header.holes[h]
    }
}

fn to_level_r(ty: &TyG<TemplateRef>) -> Result<Ty, String> {
    ty.try_map_ext(&mut |r| Err(format!("{r} in a ground position")))
}

/// Instantiation's steps 2–9 (validation is the caller's).
fn run(
    template: &Template,
    host: &mut dyn InstantiationHost,
    mode: Mode,
) -> Result<(Module, AnswerLog, BTreeMap<FuncId, FuncId>), InstantiateError> {
    let t = &template.module;
    let rows = GenericRows::of(t);
    let mut log = AnswerLog::default();
    let invalid = |why: String| {
        InstantiateError::TemplateInvalid(vec![TemplateViolation::Structure(
            TemplateError::TemplateUnsupported { what: why },
        )])
    };

    // Step 2: the seed. Ground content at its ids; every generic row a
    // placeholder until step 4.
    let mut out = Module::new(t.name.clone());
    // Nominal carriers participate in the shared level map. They remain ground
    // under T5; conversion checks that invariant again rather than cloning an S
    // row into an R module or silently substituting a missing layout contract.
    out.structs = t
        .structs
        .iter()
        .map(|row| row.try_map_level(&mut to_level_r))
        .collect::<Result<_, _>>()
        .map_err(invalid)?;
    out.enums = t
        .enums
        .iter()
        .map(|row| row.try_map_level(&mut to_level_r))
        .collect::<Result<_, _>>()
        .map_err(invalid)?;
    out.records = t.records.clone();
    out.closure_types = t.closure_types.clone();
    out.target_info = t.target_info.clone();
    out.files = t.files.clone();
    out.universes = t.universes.clone();
    out.predicates = t.predicates.clone();
    out.tuple_layouts = t.tuple_layouts.clone();
    out.drop_glue = t.drop_glue.clone();
    for (i, ty) in t.types.iter().enumerate() {
        out.types.push(if rows.types[i] {
            Ty::Error
        } else {
            to_level_r(ty).map_err(invalid)?
        });
    }
    for (i, signature) in t.func_types.iter().enumerate() {
        out.func_types.push(if rows.func_types[i] {
            FuncTy {
                abi: None,
                params: vec![Ty::Error],
                returns: vec![Ty::Error],
                is_vararg: false,
            }
        } else {
            signature
                .try_map_level(&mut |ty| to_level_r(ty))
                .map_err(invalid)?
        });
    }
    let hole_row = |name: &str| name.starts_with(TEMPLATE_HOLE_ROW_PREFIX);
    for (index, function) in t.functions.iter().enumerate() {
        if index == 0 || hole_row(&function.name) {
            out.functions.push(Function::new(
                function.id,
                format!("{RESERVED_PREFIX}{}", function.id.index()),
                function.ty,
                function.entry,
            ));
        } else {
            out.functions.push(
                function
                    .try_map_level(&mut |ty| to_level_r(ty), &mut |c, _| {
                        c.try_map_ext(&mut |r| Err(format!("{r} in a ground constant")))
                    })
                    .map_err(invalid)?,
            );
        }
    }
    for (index, global) in t.globals.iter().enumerate() {
        out.globals.push(if hole_row(&global.name) {
            Global {
                name: format!("{RESERVED_PREFIX}global.{index}"),
                ty: Ty::Error,
                mutable: global.mutable,
                initializer: None,
                linkage: Linkage::External,
                tls: None,
                align: None,
                section: None,
                visibility: Visibility::Default,
                retained: false,
            }
        } else {
            global
                .try_map_level(&mut |ty| to_level_r(ty))
                .map_err(invalid)?
        });
    }

    // Step 3: arguments, then holes (type and const holes by id, then callee
    // and global holes by id: a callee's signature may name any type hole).
    let mut sigma = Sigma {
        template,
        args: Vec::new(),
        answers: vec![None; template.header.holes.len()],
    };
    let args = ask(host, &mut out, Question::Arguments, |host, cx| {
        host.arguments(cx, &template.header.params)
    })?;
    check_arguments(&template.header.params, &args)?;
    log.arguments = args.clone();
    sigma.args = args;

    let order: Vec<usize> = (0..template.header.holes.len())
        .filter(|h| {
            matches!(
                sigma.hole(*h).kind,
                HoleKind::Type { .. } | HoleKind::Const { .. }
            )
        })
        .chain((0..template.header.holes.len()).filter(|h| {
            matches!(
                sigma.hole(*h).kind,
                HoleKind::Callee { .. } | HoleKind::Global { .. }
            )
        }))
        .collect();
    for h in order {
        let hole = sigma.hole(h).clone();
        let id = HoleId::new(u32::try_from(h).unwrap_or(u32::MAX));
        // The rows the arguments name, filled first (they name parameters and
        // lower holes only, T2).
        for arg in &hole.args {
            if let TemplateArg::Type(ty) = arg {
                fill_reachable(&sigma, &rows, ty, &mut out).map_err(invalid)?;
            }
        }
        let args: Vec<InstArg> = hole
            .args
            .iter()
            .map(|arg| sigma.arg(arg))
            .collect::<Result<_, _>>()
            .map_err(invalid)?;
        let question = Question::Hole(id);
        let answer = match &hole.kind {
            HoleKind::Type { .. } => {
                let ty = ask(host, &mut out, question, |host, cx| {
                    host.type_hole(cx, id, &hole.key, &args)
                })?;
                if ty == Ty::Error {
                    return Err(InstantiateError::AnswerContract {
                        hole: id.index(),
                        why: "the error type is not an answer".into(),
                    });
                }
                HoleAnswer::Type(ty)
            }
            HoleKind::Const { ty } => {
                let value = ask(host, &mut out, question, |host, cx| {
                    host.const_hole(cx, id, &hole.key, &args, ty)
                })?;
                scalar_fits(&value, ty, &out).map_err(|why| InstantiateError::AnswerContract {
                    hole: id.index(),
                    why,
                })?;
                HoleAnswer::Const(value)
            }
            HoleKind::Callee { decl } => {
                let row = t
                    .functions
                    .iter()
                    .find(|f| f.id == *decl)
                    .ok_or_else(|| invalid(format!("?{h} names no row")))?;
                let sig = signature(&sigma, &rows, t, row.ty, &mut out).map_err(invalid)?;
                let answer = ask(host, &mut out, question, |host, cx| {
                    host.callee_hole(cx, id, &hole.key, &args, &sig)
                })?;
                check_symbol(&answer.symbol).map_err(|why| InstantiateError::AnswerContract {
                    hole: id.index(),
                    why,
                })?;
                HoleAnswer::Callee(answer)
            }
            HoleKind::Global { decl } => {
                let row = t
                    .globals
                    .get(decl.as_usize())
                    .ok_or_else(|| invalid(format!("?{h} names no global")))?;
                fill_reachable(&sigma, &rows, &row.ty, &mut out).map_err(invalid)?;
                let ty = sigma.ty(&row.ty).map_err(invalid)?;
                let answer = ask(host, &mut out, question, |host, cx| {
                    host.global_hole(cx, id, &hole.key, &args, &ty, row.mutable)
                })?;
                check_symbol(&answer.symbol).map_err(|why| InstantiateError::AnswerContract {
                    hole: id.index(),
                    why,
                })?;
                HoleAnswer::Global(answer)
            }
        };
        log.holes.push((id, answer.clone()));
        sigma.answers[h] = Some(answer);
    }
    if mode == Mode::Skolem {
        SkolemHost::define_structured_rows(&sigma, &mut out).map_err(invalid)?;
    }

    // Step 4: substitute every generic row and the body.
    for (i, ty) in t.types.iter().enumerate() {
        if rows.types[i] {
            out.types[i] = sigma.ty(ty).map_err(invalid)?;
        }
    }
    for (i, signature) in t.func_types.iter().enumerate() {
        if rows.func_types[i] {
            out.func_types[i] = signature
                .try_map_level(&mut |ty| sigma.ty(ty))
                .map_err(invalid)?;
        }
    }

    // Step 5: contracts.
    for (h, hole) in template.header.holes.iter().enumerate() {
        if let (HoleKind::Type { contract }, Some(HoleAnswer::Type(answer))) =
            (&hole.kind, &sigma.answers[h])
        {
            check_contract(&sigma, contract, answer, &out).map_err(|why| {
                InstantiateError::AnswerContract {
                    hole: u32::try_from(h).unwrap_or(u32::MAX),
                    why,
                }
            })?;
        }
    }

    // Step 6: the hole rows and the body row.
    for (index, function) in t.functions.iter().enumerate() {
        if index == 0 {
            continue;
        }
        if let Some(h) = hole_of_row(template, function.id) {
            let Some(HoleAnswer::Callee(answer)) = &sigma.answers[h] else {
                return Err(invalid(format!("callee row of ?{h} unanswered")));
            };
            let row = &mut out.functions[index];
            row.name = answer.symbol.clone();
            row.calling_conv = answer.calling_conv;
            row.attrs = answer.attrs.clone();
            row.linkage = answer.linkage;
        }
    }
    for (index, global) in t.globals.iter().enumerate() {
        if !hole_row(&global.name) {
            continue;
        }
        let h = template
            .header
            .holes
            .iter()
            .position(
                |hole| matches!(hole.kind, HoleKind::Global { decl } if decl.as_usize() == index),
            )
            .ok_or_else(|| invalid(format!("global row {index} has no hole")))?;
        let Some(HoleAnswer::Global(answer)) = &sigma.answers[h] else {
            return Err(invalid(format!("global row of ?{h} unanswered")));
        };
        out.globals[index] = Global {
            name: answer.symbol.clone(),
            ty: sigma.ty(&global.ty).map_err(invalid)?,
            mutable: global.mutable,
            initializer: answer.initializer.clone(),
            linkage: answer.linkage,
            tls: None,
            align: answer.align,
            section: None,
            visibility: answer.visibility,
            retained: false,
        };
    }
    let template_body = &t.functions[0];
    let mut body = template_body
        .try_map_level(&mut |ty| sigma.ty(ty), &mut |c, _| sigma.constant(c))
        .map_err(invalid)?;
    let sig = out.func_types[template_body.ty.as_usize()].clone();
    let header = ask(host, &mut out, Question::Instance, |host, cx| {
        host.instance(cx, &sig)
    })?;
    check_header(&header, &sig)?;
    body.name = header.symbol.clone();
    body.linkage = header.linkage;
    body.visibility = header.visibility;
    body.calling_conv = header.calling_conv;
    body.attrs = header.attrs.clone();
    body.display_path = header.display_path.clone();
    body.body_gate = Some(header.body_gate.clone());
    out.functions[0] = body;
    log.header = Some(header);

    let created = if mode == Mode::Real {
        created_tuples(template, &out)
    } else {
        Vec::new()
    };

    // Step 7: one row per symbol.
    let functions = merge_by_symbol(&mut out)?;

    // Step 8: the drop rewrite (review R1, R2).
    if mode == Mode::Real {
        rewrite_drops(template_body, &mut out, host, &mut log)?;
    }

    // Step 9: declared layouts of the tuples substitution created.
    if mode == Mode::Real {
        declare_new_tuples(created, &mut out, host, &mut log)?;
    }

    Ok((out, log, functions))
}

/// Ask the host one question and check its edits were appends only.
fn ask<A>(
    host: &mut dyn InstantiationHost,
    out: &mut Module,
    question: Question,
    call: impl FnOnce(&mut dyn InstantiationHost, &mut Module) -> Result<A, HostRefusal>,
) -> Result<A, InstantiateError> {
    let before = out.clone();
    let answer = call(host, out).map_err(|HostRefusal(why)| InstantiateError::HostRefused {
        question: question.clone(),
        why,
    })?;
    append_only(&before, out).map_err(|why| InstantiateError::HostRowsInvalid { question, why })?;
    Ok(answer)
}

/// The host may append rows, never change or remove one, and never touch the
/// proof surface or the module's own facts.
fn append_only(before: &Module, after: &Module) -> Result<(), String> {
    fn prefix<T: PartialEq>(table: &str, before: &[T], after: &[T]) -> Result<(), String> {
        if after.len() < before.len() || after[..before.len()] != *before {
            return Err(format!("the {table} table lost or changed a row"));
        }
        Ok(())
    }
    if before.name != after.name
        || before.target_info != after.target_info
        || before.completeness != after.completeness
    {
        return Err("a module-level fact changed".into());
    }
    if before.proof_obligations != after.proof_obligations
        || before.proof_certificates != after.proof_certificates
        || before.obligation_diagnostics != after.obligation_diagnostics
        || before.spec_modules != after.spec_modules
        || before.global_asm != after.global_asm
        || before.imports != after.imports
    {
        return Err(
            "the proof surface changed (a host answers types, constants and names only)".into(),
        );
    }
    prefix("function", &before.functions, &after.functions)?;
    prefix("struct", &before.structs, &after.structs)?;
    prefix("enum", &before.enums, &after.enums)?;
    prefix("record", &before.records, &after.records)?;
    prefix("closure-type", &before.closure_types, &after.closure_types)?;
    prefix("global", &before.globals, &after.globals)?;
    prefix("function-type", &before.func_types, &after.func_types)?;
    prefix("type", &before.types, &after.types)?;
    prefix("file", &before.files, &after.files)?;
    prefix("universe", &before.universes, &after.universes)?;
    prefix("predicate", &before.predicates, &after.predicates)?;
    prefix("tuple-layout", &before.tuple_layouts, &after.tuple_layouts)?;
    prefix("drop-glue", &before.drop_glue, &after.drop_glue)?;
    for function in &after.functions[before.functions.len()..] {
        if !function.blocks.is_empty() {
            return Err(format!(
                "`{}` is a definition; a host appends declarations only",
                function.name
            ));
        }
        check_symbol(&function.name)?;
    }
    for global in &after.globals[before.globals.len()..] {
        check_symbol(&global.name)?;
    }
    Ok(())
}

/// A host-supplied symbol: nonempty, and never a template's reserved name.
fn check_symbol(symbol: &str) -> Result<(), String> {
    if symbol.is_empty() {
        return Err("an empty symbol".into());
    }
    if symbol.starts_with("!template_") {
        return Err(format!(
            "`{symbol}` is a reserved template name, not a link symbol"
        ));
    }
    Ok(())
}

fn check_arguments(params: &[TemplateParam], args: &[InstArg]) -> Result<(), InstantiateError> {
    if params.len() != args.len() {
        return Err(InstantiateError::ArityMismatch {
            expected: params.len(),
            got: args.len(),
        });
    }
    for (i, (param, arg)) in params.iter().zip(args).enumerate() {
        let param_id = u32::try_from(i).unwrap_or(u32::MAX);
        let kind = |why: &str| InstantiateError::ArgumentKind {
            param: param_id,
            why: why.to_string(),
        };
        match (param, arg) {
            (TemplateParam::Type, InstArg::Type(ty)) => {
                if *ty == Ty::Error {
                    return Err(kind("the error type is not an argument"));
                }
            }
            (TemplateParam::Const { ty }, InstArg::Const(value)) => {
                // The output's own validation re-checks every use; this is
                // the scalar range the parameter's type admits.
                scalar_fits(value, ty, &Module::new("")).map_err(|why| {
                    InstantiateError::ArgumentKind {
                        param: param_id,
                        why,
                    }
                })?;
            }
            (TemplateParam::Host, InstArg::Host(key)) => {
                if !key.namespace_is_valid() {
                    return Err(kind("a host key namespace outside [A-Za-z0-9_.]+"));
                }
            }
            (TemplateParam::Type, _) => return Err(kind("a type parameter takes a type")),
            (TemplateParam::Const { .. }, _) => {
                return Err(kind("a const parameter takes a constant"));
            }
            (TemplateParam::Host, _) => return Err(kind("a host parameter takes a host key")),
        }
    }
    Ok(())
}

/// Whether `value` is a constant of the scalar type `ty` (const parameters
/// and const holes are scalar-typed, T8).
fn scalar_fits(value: &Constant, ty: &Ty, cx: &Module) -> Result<(), String> {
    if !is_template_scalar(ty) {
        return Err(format!("{ty} is not a template scalar"));
    }
    let pointer_bits = cx
        .target_info
        .as_ref()
        .map_or(64, |info| info.pointer_size.saturating_mul(8));
    let int_range = |ty: &Ty| -> Option<(i128, u128, bool)> {
        let (bits, signed) = match ty {
            Ty::I8 => (8, true),
            Ty::I16 => (16, true),
            Ty::I32 => (32, true),
            Ty::I64 => (64, true),
            Ty::I128 => (128, true),
            Ty::Isize => (pointer_bits, true),
            Ty::U8 => (8, false),
            Ty::U16 => (16, false),
            Ty::U32 => (32, false),
            Ty::U64 => (64, false),
            Ty::U128 => (128, false),
            Ty::Usize => (pointer_bits, false),
            _ => return None,
        };
        if signed {
            let min = if bits >= 128 {
                i128::MIN
            } else {
                -(1i128 << (bits - 1))
            };
            let max = if bits >= 128 {
                i128::MAX as u128
            } else {
                (1u128 << (bits - 1)) - 1
            };
            Some((min, max, true))
        } else {
            let max = if bits >= 128 {
                u128::MAX
            } else {
                (1u128 << bits) - 1
            };
            Some((0, max, false))
        }
    };
    let fits = match (value, ty) {
        (Constant::Bool(_), Ty::Bool) => true,
        (Constant::Float(_), Ty::F16 | Ty::F32 | Ty::F64) => true,
        (Constant::Int(v), Ty::Char) => u32::try_from(*v).ok().and_then(char::from_u32).is_some(),
        (Constant::Int(v), _) => {
            int_range(ty).is_some_and(|(min, max, _)| *v >= min && (*v < 0 || (*v as u128) <= max))
        }
        (Constant::U128(v), Ty::U128) => *v > i128::MAX as u128,
        _ => false,
    };
    if fits {
        Ok(())
    } else {
        Err(format!("{value} is not a constant of type {ty}"))
    }
}

/// Fill (substitute in place) every generic `types` / `func_types` row
/// reachable from `ty` whose own references are answered.
fn fill_reachable(
    sigma: &Sigma<'_>,
    rows: &GenericRows,
    ty: &TyG<TemplateRef>,
    out: &mut Module,
) -> Result<(), String> {
    let t = &sigma.template.module;
    let mut ty_rows = Vec::new();
    let mut fty_rows = Vec::new();
    ty.for_each_row(&mut |r| ty_rows.push(r), &mut |r| fty_rows.push(r));
    let mut seen_ty = BTreeSet::new();
    let mut seen_fty = BTreeSet::new();
    while !ty_rows.is_empty() || !fty_rows.is_empty() {
        if let Some(row) = ty_rows.pop() {
            if !seen_ty.insert(row.index()) {
                continue;
            }
            let Some(template_row) = t.types.get(row.as_usize()) else {
                continue;
            };
            if rows.types[row.as_usize()] {
                out.types[row.as_usize()] = sigma.ty(template_row)?;
            }
            template_row.for_each_row(&mut |r| ty_rows.push(r), &mut |r| fty_rows.push(r));
        } else if let Some(row) = fty_rows.pop() {
            if !seen_fty.insert(row.index()) {
                continue;
            }
            let Some(template_row) = t.func_types.get(row.as_usize()) else {
                continue;
            };
            if rows.func_types[row.as_usize()] {
                out.func_types[row.as_usize()] =
                    template_row.try_map_level(&mut |ty| sigma.ty(ty))?;
            }
            for ty in template_row.params.iter().chain(&template_row.returns) {
                ty.for_each_row(&mut |r| ty_rows.push(r), &mut |r| fty_rows.push(r));
            }
        }
    }
    Ok(())
}

/// A row's signature, substituted (its reachable rows filled first).
fn signature(
    sigma: &Sigma<'_>,
    rows: &GenericRows,
    t: &trust_ir::ModuleG<TemplateRef>,
    row: FuncTyId,
    out: &mut Module,
) -> Result<FuncTy, String> {
    let template_row = t
        .func_types
        .get(row.as_usize())
        .ok_or_else(|| format!("functy.{} does not exist", row.index()))?;
    for ty in template_row.params.iter().chain(&template_row.returns) {
        fill_reachable(sigma, rows, ty, out)?;
    }
    template_row.try_map_level(&mut |ty| sigma.ty(ty))
}

fn hole_of_row(template: &Template, row: FuncId) -> Option<usize> {
    template
        .header
        .holes
        .iter()
        .position(|hole| matches!(hole.kind, HoleKind::Callee { decl } if decl == row))
}

/// Step 5: an answer satisfies its hole's contract.
fn check_contract(
    sigma: &Sigma<'_>,
    contract: &TypeContract,
    answer: &Ty,
    out: &Module,
) -> Result<(), String> {
    match contract {
        TypeContract::Opaque => Ok(()),
        TypeContract::ThinPointer => {
            if *answer == Ty::Ptr {
                Ok(())
            } else {
                Err(format!("{answer} is not a thin pointer"))
            }
        }
        TypeContract::Struct { fields } => {
            let Ty::Struct(id) = answer else {
                return Err(format!("{answer} is not a struct"));
            };
            let def = out
                .structs
                .iter()
                .find(|sd| sd.id == *id)
                .ok_or_else(|| format!("struct.{} has no row", id.index()))?;
            let expected: Vec<Ty> = fields
                .iter()
                .map(|ty| sigma.ty(ty))
                .collect::<Result<_, _>>()?;
            let got: Vec<Ty> = def.fields.iter().map(|field| field.ty.clone()).collect();
            if got != expected {
                return Err(format!(
                    "struct `{}` has fields ({}), the contract says ({})",
                    def.name,
                    join(&got),
                    join(&expected)
                ));
            }
            Ok(())
        }
        TypeContract::Enum {
            variants,
            discriminants,
            repr,
        } => {
            let Ty::Enum(id) = answer else {
                return Err(format!("{answer} is not an enum"));
            };
            let def = out
                .enums
                .iter()
                .find(|ed| ed.id == *id)
                .ok_or_else(|| format!("enum.{} has no row", id.index()))?;
            if def.variants.len() != variants.len() {
                return Err(format!(
                    "enum `{}` has {} variants, the contract says {}",
                    def.name,
                    def.variants.len(),
                    variants.len()
                ));
            }
            for (index, (variant, expected)) in def.variants.iter().zip(variants).enumerate() {
                let expected: Vec<Ty> = expected
                    .iter()
                    .map(|ty| sigma.ty(ty))
                    .collect::<Result<_, _>>()?;
                if variant.fields != expected {
                    return Err(format!(
                        "variant {index} of enum `{}` has fields ({}), the contract says ({})",
                        def.name,
                        join(&variant.fields),
                        join(&expected)
                    ));
                }
            }
            if def.discriminants != *discriminants {
                return Err(format!(
                    "enum `{}` declares discriminants {:?}, the contract says {:?} (the body's \
                     switch reads them)",
                    def.name, def.discriminants, discriminants
                ));
            }
            if def.repr != *repr {
                return Err(format!(
                    "enum `{}` declares repr {:?}, the contract says {:?} (the tag width the \
                     body reads)",
                    def.name, def.repr, repr
                ));
            }
            Ok(())
        }
    }
}

fn join(tys: &[Ty]) -> String {
    tys.iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(", ")
}

fn check_header(header: &InstanceHeader, sig: &FuncTy) -> Result<(), InstantiateError> {
    let why = |why: String| InstantiateError::InstanceHeader { why };
    check_symbol(&header.symbol).map_err(why)?;
    if !header.attrs.params.is_empty() && header.attrs.params.len() != sig.params.len() {
        return Err(why(format!(
            "{} parameter attributes for a signature of {} parameters",
            header.attrs.params.len(),
            sig.params.len()
        )));
    }
    Ok(())
}

/// Step 7: rows sharing a symbol become one (review R8).
fn merge_by_symbol(out: &mut Module) -> Result<BTreeMap<FuncId, FuncId>, InstantiateError> {
    let conflict = |why: String| InstantiateError::AnswerConflict { why };
    // Functions.
    let mut by_symbol: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for (index, function) in out.functions.iter().enumerate() {
        by_symbol
            .entry(function.name.clone())
            .or_default()
            .push(index);
    }
    let mut redirect: BTreeMap<FuncId, FuncId> = BTreeMap::new();
    let original_functions: Vec<_> = out.functions.iter().map(|function| function.id).collect();
    let mut drop_rows: BTreeSet<usize> = BTreeSet::new();
    for (symbol, indices) in &by_symbol {
        if indices.len() < 2 {
            continue;
        }
        let definitions: Vec<usize> = indices
            .iter()
            .copied()
            .filter(|i| !out.functions[*i].blocks.is_empty())
            .collect();
        if definitions.len() > 1 {
            return Err(conflict(format!("`{symbol}` names two definitions")));
        }
        let keep = definitions.first().copied().unwrap_or_else(|| {
            *indices
                .iter()
                .min_by_key(|i| out.functions[**i].id.index())
                .expect("two rows")
        });
        let kept = &out.functions[keep];
        let kept_sig = out.func_types.get(kept.ty.as_usize()).cloned();
        for &other in indices {
            if other == keep {
                continue;
            }
            let row = &out.functions[other];
            let sig = out.func_types.get(row.ty.as_usize()).cloned();
            if sig != kept_sig {
                return Err(conflict(format!(
                    "`{symbol}` is declared with two signatures"
                )));
            }
            if row.calling_conv != kept.calling_conv
                || row.attrs != kept.attrs
                || (kept.blocks.is_empty() && row.linkage != kept.linkage)
            {
                return Err(conflict(format!(
                    "`{symbol}` is declared with two conventions, attribute sets or linkages"
                )));
            }
            redirect.insert(row.id, kept.id);
            drop_rows.insert(other);
        }
    }
    if !redirect.is_empty() {
        let mut index = 0;
        out.functions.retain(|_| {
            let keep = !drop_rows.contains(&index);
            index += 1;
            keep
        });
        remap_func_ids(out, &redirect);
    }
    // Globals (positional ids).
    let mut first_of: BTreeMap<String, usize> = BTreeMap::new();
    let mut global_redirect: BTreeMap<u32, u32> = BTreeMap::new();
    for (index, global) in out.globals.iter().enumerate() {
        match first_of.get(&global.name) {
            None => {
                first_of.insert(global.name.clone(), index);
            }
            Some(&first) => {
                let kept = &out.globals[first];
                if kept.ty != global.ty
                    || kept.mutable != global.mutable
                    || kept.initializer != global.initializer
                    || kept.linkage != global.linkage
                {
                    return Err(conflict(format!(
                        "global `{}` is answered twice with different facts",
                        global.name
                    )));
                }
                global_redirect.insert(
                    u32::try_from(index).unwrap_or(u32::MAX),
                    u32::try_from(first).unwrap_or(u32::MAX),
                );
            }
        }
    }
    if !global_redirect.is_empty() {
        let mut new_index: Vec<u32> = Vec::with_capacity(out.globals.len());
        let mut next = 0u32;
        for index in 0..out.globals.len() {
            let index32 = u32::try_from(index).unwrap_or(u32::MAX);
            if global_redirect.contains_key(&index32) {
                new_index.push(u32::MAX);
            } else {
                new_index.push(next);
                next += 1;
            }
        }
        let map = |old: u32| -> u32 {
            let target = global_redirect.get(&old).copied().unwrap_or(old);
            new_index[target as usize]
        };
        let mut index = 0u32;
        out.globals.retain(|_| {
            let keep = !global_redirect.contains_key(&index);
            index += 1;
            keep
        });
        remap_global_ids(out, &map);
    }
    Ok(original_functions
        .into_iter()
        .map(|id| (id, redirect.get(&id).copied().unwrap_or(id)))
        .collect())
}

fn remap_constant_funcs(c: &mut Constant, redirect: &BTreeMap<FuncId, FuncId>) {
    match c {
        Constant::FnDef(func) | Constant::FnItem(func) => {
            if let Some(to) = redirect.get(func) {
                *func = *to;
            }
        }
        Constant::Closure { func, captures } => {
            if let Some(to) = redirect.get(func) {
                *func = *to;
            }
            captures
                .iter_mut()
                .for_each(|c| remap_constant_funcs(c, redirect));
        }
        Constant::Aggregate(items)
        | Constant::Array(items)
        | Constant::Vector(items)
        | Constant::Sequence(items)
        | Constant::Set(items) => items
            .iter_mut()
            .for_each(|c| remap_constant_funcs(c, redirect)),
        Constant::Record(fields) => fields
            .iter_mut()
            .for_each(|(_, c)| remap_constant_funcs(c, redirect)),
        Constant::Splat { elem, .. } => remap_constant_funcs(elem, redirect),
        Constant::Int(_)
        | Constant::U128(_)
        | Constant::Bytes { .. }
        | Constant::Float(_)
        | Constant::Bool(_)
        | Constant::SymbolAddr { .. }
        | Constant::PhantomData
        | Constant::Uninit
        | Constant::TensorBlob { .. } => {}
        Constant::Ext(e) => e.unreachable(),
    }
}

/// Every `FuncId` a module names, redirected.
fn remap_func_ids(out: &mut Module, redirect: &BTreeMap<FuncId, FuncId>) {
    let to = |id: &mut FuncId| {
        if let Some(target) = redirect.get(id) {
            *id = *target;
        }
    };
    // Function-item identity is also part of a type, including unused source
    // rows and nested aggregate fields. Relocate every stored spelling before
    // rewriting the value/edge that uses it.
    for ty in &mut out.types {
        remap_ty_funcs(ty, redirect);
    }
    for signature in &mut out.func_types {
        for ty in signature.params.iter_mut().chain(&mut signature.returns) {
            remap_ty_funcs(ty, redirect);
        }
    }
    for row in &mut out.structs {
        for field in &mut row.fields {
            remap_ty_funcs(&mut field.ty, redirect);
        }
    }
    for row in &mut out.records {
        for field in &mut row.fields {
            remap_ty_funcs(&mut field.ty, redirect);
        }
    }
    for row in &mut out.enums {
        for variant in &mut row.variants {
            for ty in &mut variant.fields {
                remap_ty_funcs(ty, redirect);
            }
        }
    }
    for row in &mut out.closure_types {
        for ty in &mut row.captures {
            remap_ty_funcs(ty, redirect);
        }
    }
    for row in &mut out.globals {
        remap_ty_funcs(&mut row.ty, redirect);
    }
    for row in &mut out.drop_glue {
        remap_ty_funcs(&mut row.ty, redirect);
    }
    for function in &mut out.functions {
        for block in &mut function.blocks {
            for (_, ty) in &mut block.params {
                remap_ty_funcs(ty, redirect);
            }
            for node in &mut block.body {
                let mut has_item = false;
                node.inst.for_each_ty(|ty| {
                    ty.visit_types(|child| {
                        has_item |= matches!(child, Ty::FnItem(_));
                    })
                });
                if has_item {
                    let mapped = node.inst.try_map_level(
                        &mut |ty| {
                            let mut mapped = ty.clone();
                            remap_ty_funcs(&mut mapped, redirect);
                            Ok::<_, core::convert::Infallible>(mapped)
                        },
                        &mut |value, _| Ok(value.clone()),
                    );
                    node.inst = mapped.unwrap_or_else(|never| match never {});
                }
                match &mut node.inst {
                    Inst::OpenFrame { def } => {
                        for slot in &mut def.slots {
                            remap_ty_funcs(&mut slot.ty, redirect);
                        }
                    }
                    Inst::DialectOp(op) => {
                        for ty in &mut op.result_tys {
                            remap_ty_funcs(ty, redirect);
                        }
                        for attr in &mut op.attrs {
                            if let trust_ir::dialect::AttrValue::Ty(ty) = &mut attr.value {
                                remap_ty_funcs(ty, redirect);
                            }
                        }
                    }
                    Inst::Call { callee, .. }
                    | Inst::CallCannotUnwind { callee, .. }
                    | Inst::Invoke { callee, .. } => to(callee),
                    Inst::SeqMap { fwd, .. } => to(fwd),
                    Inst::MakeClosure { func, .. } => to(func),
                    Inst::Assert {
                        site: Some(site), ..
                    }
                    | Inst::AssertInvoke { site, .. } => {
                        to(&mut site.entry);
                    }
                    Inst::Const { value, .. } => remap_constant_funcs(value, redirect),
                    _ => {}
                }
            }
        }
    }
    for global in &mut out.globals {
        if let Some(init) = &mut global.initializer {
            remap_constant_funcs(init, redirect);
        }
    }
    for entry in &mut out.drop_glue {
        to(&mut entry.glue);
    }
    out.drop_glue.sort_by_key(|entry| entry.glue.index());
}

fn remap_ty_funcs(root: &mut Ty, redirect: &BTreeMap<FuncId, FuncId>) {
    let mut pending = vec![root];
    while let Some(ty) = pending.pop() {
        match ty {
            Ty::FnItem(id) => {
                if let Some(mapped) = redirect.get(id) {
                    *id = *mapped;
                }
            }
            Ty::Tuple(fields) => pending.extend(fields.iter_mut()),
            Ty::Vector(inner, _)
            | Ty::Ref(inner)
            | Ty::RefMut(inner)
            | Ty::PtrConst(inner)
            | Ty::PtrMut(inner)
            | Ty::Rc(inner) => pending.push(inner),
            _ => {}
        }
    }
}

/// Every `GlobalId` a module names, through `map`.
fn remap_global_ids(out: &mut Module, map: &dyn Fn(u32) -> u32) {
    for function in &mut out.functions {
        for block in &mut function.blocks {
            for node in &mut block.body {
                match &mut node.inst {
                    Inst::GlobalAddr { global } => {
                        *global = trust_ir::value::GlobalId::new(map(global.index()))
                    }
                    Inst::Assert {
                        site: Some(site), ..
                    }
                    | Inst::AssertInvoke { site, .. } => {
                        if let trust_ir::PanicLocation::Global(global) = &mut site.location {
                            *global = trust_ir::value::GlobalId::new(map(global.index()));
                        }
                    }
                    _ => {}
                }
            }
        }
    }
}

/// Step 8: the drop rewrite (S7, review R1 and R2).
fn rewrite_drops(
    template_body: &FunctionG<TemplateRef>,
    out: &mut Module,
    host: &mut dyn InstantiationHost,
    log: &mut AnswerLog,
) -> Result<(), InstantiateError> {
    // Which drops are parameter-dependent: by position in the template body.
    let mut generic_sites: BTreeSet<(u32, usize)> = BTreeSet::new();
    for block in &template_body.blocks {
        for (index, node) in block.body.iter().enumerate() {
            if let InstG::Drop { ty, .. } | InstG::DropInvoke { ty, .. } = &node.inst {
                let mut generic = false;
                ty.for_each_ext(&mut |_| generic = true);
                if generic {
                    generic_sites.insert((block.id.index(), index));
                }
            }
        }
    }
    if generic_sites.is_empty() {
        return Ok(());
    }
    let mut decisions: BTreeMap<String, bool> = BTreeMap::new(); // type text -> erase?
    let mut erase_sites: BTreeSet<(u32, usize)> = BTreeSet::new();
    let mut retyped: BTreeMap<(u32, usize), Ty> = BTreeMap::new();
    let body_blocks: Vec<(u32, Vec<(usize, Ty)>)> = out.functions[0]
        .blocks
        .iter()
        .map(|block| {
            (
                block.id.index(),
                block
                    .body
                    .iter()
                    .enumerate()
                    .filter_map(|(i, node)| match &node.inst {
                        Inst::Drop { ty, .. } | Inst::DropInvoke { ty, .. } => {
                            Some((i, ty.clone()))
                        }
                        _ => None,
                    })
                    .collect(),
            )
        })
        .collect();
    for (block, drops) in body_blocks {
        for (index, ty) in drops {
            if !generic_sites.contains(&(block, index)) {
                continue;
            }
            // §20's spelling of a drop of a refinement: at its base.
            let mut ty = ty;
            while let Ty::Refine(base, _) = &ty {
                match out.types.get(base.as_usize()) {
                    Some(base_ty) => ty = base_ty.clone(),
                    None => break,
                }
            }
            if ty != Ty::Error {
                retyped.insert((block, index), ty.clone());
            }
            let erase = if ty.is_trivially_droppable(&out.types) {
                true
            } else if matches!(
                out.drop_glue_for(&ty),
                trust_ir::DropResolution::Resolved(_)
            ) {
                false
            } else if let Some(decided) = decisions.get(&ty.to_string()) {
                *decided
            } else {
                let question = Question::Destructor(ty.clone());
                let answer = ask(host, out, question, |host, cx| host.destructor(cx, &ty))?;
                log.destructors.push((ty.clone(), answer.clone()));
                let erase = match answer {
                    Destructor::NoDestructor => true,
                    Destructor::Glue(link) => {
                        add_glue(out, &ty, &link)?;
                        false
                    }
                };
                decisions.insert(ty.to_string(), erase);
                erase
            };
            if erase {
                erase_sites.insert((block, index));
            }
        }
    }
    let body = &mut out.functions[0];
    for block in &mut body.blocks {
        let block_id = block.id.index();
        let mut kept = Vec::with_capacity(block.body.len());
        for (index, mut node) in std::mem::take(&mut block.body).into_iter().enumerate() {
            if let Some(ty) = retyped.get(&(block_id, index))
                && let Inst::Drop { ty: slot, .. } | Inst::DropInvoke { ty: slot, .. } =
                    &mut node.inst
            {
                *slot = ty.clone();
            }
            if erase_sites.contains(&(block_id, index)) {
                match node.inst {
                    Inst::Drop { .. } => continue,
                    Inst::DropInvoke {
                        normal_dest,
                        normal_args,
                        ..
                    } => {
                        node.inst = Inst::Br {
                            target: normal_dest,
                            args: normal_args,
                        };
                    }
                    _ => {}
                }
            }
            kept.push(node);
        }
        block.body = kept;
    }
    delete_unreachable_blocks(body);
    Ok(())
}

/// A destructor's glue: a `(ptr) -> ()` declaration named by the answer (one
/// row per symbol) and its drop-glue row.
fn add_glue(out: &mut Module, ty: &Ty, link: &LinkAnswer) -> Result<(), InstantiateError> {
    let conflict = |why: String| InstantiateError::AnswerConflict { why };
    check_symbol(&link.symbol).map_err(conflict)?;
    let glue_sig = FuncTy {
        abi: None,
        params: vec![Ty::Ptr],
        returns: vec![],
        is_vararg: false,
    };
    let glue = match out.functions.iter().find(|f| f.name == link.symbol) {
        Some(existing) => {
            if out.func_types.get(existing.ty.as_usize()) != Some(&glue_sig) {
                return Err(conflict(format!(
                    "`{}` is a destructor and a function of another signature",
                    link.symbol
                )));
            }
            existing.id
        }
        None => {
            let ty_id = out.intern_func_type(glue_sig).map_err(|exhausted| {
                conflict(format!(
                    "the destructor `{}` cannot be declared: {exhausted}",
                    link.symbol
                ))
            })?;
            let id = FuncId::new(
                out.functions
                    .iter()
                    .map(|f| f.id.index() + 1)
                    .max()
                    .unwrap_or(0),
            );
            let mut decl = Function::new(id, link.symbol.clone(), ty_id, BlockId::new(0));
            decl.calling_conv = link.calling_conv;
            decl.attrs = link.attrs.clone();
            decl.linkage = link.linkage;
            out.functions.push(decl);
            id
        }
    };
    out.set_drop_glue(ty.clone(), glue)
        .map_err(|error| conflict(format!("the destructor of {ty}: {error:?}")))
}

/// Delete the blocks erasure left unreachable from the entry (review R2):
/// erasure only removes edges, so a block reachable afterwards was reachable
/// before by the same path, and every definition a kept use reads is kept.
fn delete_unreachable_blocks(function: &mut Function) {
    let mut reachable: BTreeSet<BlockId> = BTreeSet::new();
    let mut work = vec![function.entry];
    while let Some(block_id) = work.pop() {
        if !reachable.insert(block_id) {
            continue;
        }
        let Some(block) = function.blocks.iter().find(|b| b.id == block_id) else {
            continue;
        };
        for node in &block.body {
            for edge in node.inst.successor_edges() {
                work.push(edge.target);
            }
        }
    }
    function
        .blocks
        .retain(|block| reachable.contains(&block.id));
}

/// The tuple types substitution created (review: step 9): every tuple node of
/// an instance type whose template counterpart spells a parameter or hole
/// inside the tuple itself, paired position by position. Run right after
/// step 6, while the body still has the template's shape.
fn created_tuples(template: &Template, out: &Module) -> Vec<Ty> {
    let t = &template.module;
    let mut created = Vec::new();
    let body = &out.functions[0];
    let template_body = &t.functions[0];
    for (template_block, block) in template_body.blocks.iter().zip(&body.blocks) {
        for ((_, tt), (_, it)) in template_block.params.iter().zip(&block.params) {
            collect_new_tuples(tt, it, &mut created);
        }
        for (template_node, node) in template_block.body.iter().zip(&block.body) {
            let mut tts = Vec::new();
            template_node.inst.for_each_ty(|ty| tts.push(ty));
            let mut its = Vec::new();
            node.inst.for_each_ty(|ty| its.push(ty));
            for (tt, it) in tts.into_iter().zip(its) {
                collect_new_tuples(tt, it, &mut created);
            }
        }
    }
    for (tt, it) in t.types.iter().zip(&out.types) {
        collect_new_tuples(tt, it, &mut created);
    }
    for (signature, filled) in t.func_types.iter().zip(&out.func_types) {
        for (tt, it) in signature
            .params
            .iter()
            .chain(&signature.returns)
            .zip(filled.params.iter().chain(&filled.returns))
        {
            collect_new_tuples(tt, it, &mut created);
        }
    }
    for (tg, ig) in t.globals.iter().zip(&out.globals) {
        collect_new_tuples(&tg.ty, &ig.ty, &mut created);
    }
    let mut seen = BTreeSet::new();
    created.retain(|ty| seen.insert(ty.to_string()));
    created
}

/// Step 9: a declared layout for each created tuple type that has none.
fn declare_new_tuples(
    created: Vec<Ty>,
    out: &mut Module,
    host: &mut dyn InstantiationHost,
    log: &mut AnswerLog,
) -> Result<(), InstantiateError> {
    for tuple in created {
        let declared = out
            .tuple_layouts
            .iter()
            .any(|layout| out.types.get(layout.tuple_type.as_usize()) == Some(&tuple));
        if declared {
            continue;
        }
        let question = Question::TupleLayout(tuple.clone());
        let answer = ask(host, out, question, |host, cx| {
            host.tuple_layout(cx, &tuple)
        })?;
        log.tuple_layouts.push((tuple.clone(), answer.clone()));
        if let Some(layout) = answer {
            let tuple_type = match out.types.iter().position(|ty| *ty == tuple) {
                Some(index) => TyId::new(u32::try_from(index).unwrap_or(u32::MAX)),
                None => out.add_type(tuple.clone()).map_err(|exhausted| {
                    InstantiateError::AnswerConflict {
                        why: format!("the tuple layout of {tuple} cannot be recorded: {exhausted}"),
                    }
                })?,
            };
            out.tuple_layouts.push(trust_ir::TupleLayoutDescriptor {
                tuple_type,
                size: layout.size,
                align: layout.align,
                field_offsets: layout.field_offsets,
            });
        }
    }
    Ok(())
}

/// The tuple nodes of `it` whose template counterpart in `tt` spells a
/// parameter or hole inside the tuple itself.
fn collect_new_tuples(tt: &TyG<TemplateRef>, it: &Ty, out: &mut Vec<Ty>) {
    match (tt, it) {
        (TyG::Tuple(ts), Ty::Tuple(is)) => {
            let mut direct = false;
            for t in ts {
                t.for_each_ext(&mut |_| direct = true);
            }
            if direct {
                out.push(it.clone());
            }
            for (t, i) in ts.iter().zip(is) {
                collect_new_tuples(t, i, out);
            }
        }
        (TyG::Vector(t, _), Ty::Vector(i, _))
        | (TyG::Tensor(t, _), Ty::Tensor(i, _))
        | (TyG::Ref(t), Ty::Ref(i))
        | (TyG::RefMut(t), Ty::RefMut(i))
        | (TyG::PtrConst(t), Ty::PtrConst(i))
        | (TyG::PtrMut(t), Ty::PtrMut(i))
        | (TyG::Rc(t), Ty::Rc(i)) => collect_new_tuples(t, i, out),
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// The skolem host (T6, review R11)
// ---------------------------------------------------------------------------

struct SkolemHost<'t> {
    template: &'t Template,
}

impl<'t> SkolemHost<'t> {
    fn new(template: &'t Template) -> Self {
        Self { template }
    }

    fn fresh_struct(cx: &mut Module, name: String) -> Result<Ty, HostRefusal> {
        let id = cx
            .allocate_struct_id()
            .map_err(|exhausted| HostRefusal(exhausted.to_string()))?;
        cx.structs.push(StructDef {
            id,
            name,
            fields: vec![],
            size: None,
            align: None,
            repr: StructRepr::Rust,
            origin: None,
        });
        Ok(Ty::Struct(id))
    }

    fn skolem_constant(ty: &Ty) -> Constant {
        match ty {
            Ty::Bool => Constant::Bool(true),
            Ty::F16 | Ty::F32 | Ty::F64 => Constant::Float(1.0),
            Ty::Char => Constant::Int(i128::from(u32::from('a'))),
            _ => Constant::Int(1),
        }
    }

    /// After every hole is answered: the structured holes' skolem rows get
    /// exactly their contracts (fields may name any hole, review R6).
    fn define_structured_rows(sigma: &Sigma<'_>, out: &mut Module) -> Result<(), String> {
        for (h, hole) in sigma.template.header.holes.iter().enumerate() {
            let (HoleKind::Type { contract }, Some(HoleAnswer::Type(answer))) =
                (&hole.kind, &sigma.answers[h])
            else {
                continue;
            };
            match (contract, answer) {
                (TypeContract::Struct { fields }, Ty::Struct(id)) => {
                    let fields = fields
                        .iter()
                        .enumerate()
                        .map(|(i, ty)| {
                            Ok(trust_ir::FieldDef {
                                name: format!("f{i}"),
                                ty: sigma.ty(ty)?,
                                offset: None,
                            })
                        })
                        .collect::<Result<Vec<_>, String>>()?;
                    if let Some(def) = out.structs.iter_mut().find(|sd| sd.id == *id) {
                        def.fields = fields;
                    }
                }
                (
                    TypeContract::Enum {
                        variants,
                        discriminants,
                        repr,
                    },
                    Ty::Enum(id),
                ) => {
                    let variants = variants
                        .iter()
                        .enumerate()
                        .map(|(i, fields)| {
                            Ok(trust_ir::EnumVariant {
                                name: format!("V{i}"),
                                fields: fields
                                    .iter()
                                    .map(|ty| sigma.ty(ty))
                                    .collect::<Result<_, String>>()?,
                                field_names: vec![],
                            })
                        })
                        .collect::<Result<Vec<_>, String>>()?;
                    if let Some(def) = out.enums.iter_mut().find(|ed| ed.id == *id) {
                        def.variants = variants;
                        def.discriminants = discriminants.clone();
                        def.repr = *repr;
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }
}

impl InstantiationHost for SkolemHost<'_> {
    fn arguments(
        &mut self,
        cx: &mut Module,
        params: &[TemplateParam],
    ) -> Result<Vec<InstArg>, HostRefusal> {
        params
            .iter()
            .enumerate()
            .map(|(p, param)| {
                Ok(match param {
                    TemplateParam::Type => {
                        InstArg::Type(Self::fresh_struct(cx, format!("__skolem_param_{p}"))?)
                    }
                    TemplateParam::Const { ty } => InstArg::Const(Self::skolem_constant(ty)),
                    TemplateParam::Host => InstArg::Host(HostKey::new("skolem", vec![])),
                })
            })
            .collect()
    }

    fn type_hole(
        &mut self,
        cx: &mut Module,
        hole: HoleId,
        _key: &HostKey,
        _args: &[InstArg],
    ) -> Result<Ty, HostRefusal> {
        let name = format!("__skolem_hole_{}", hole.index());
        match &self.template.header.holes[hole.as_usize()].kind {
            HoleKind::Type {
                contract: TypeContract::ThinPointer,
            } => Ok(Ty::Ptr),
            HoleKind::Type {
                contract: TypeContract::Enum { .. },
            } => {
                let id = cx
                    .allocate_enum_id()
                    .map_err(|exhausted| HostRefusal(exhausted.to_string()))?;
                cx.enums.push(EnumDef::new(id, name, vec![]));
                Ok(Ty::Enum(id))
            }
            _ => Self::fresh_struct(cx, name),
        }
    }

    fn const_hole(
        &mut self,
        _cx: &mut Module,
        _hole: HoleId,
        _key: &HostKey,
        _args: &[InstArg],
        ty: &Ty,
    ) -> Result<Constant, HostRefusal> {
        Ok(Self::skolem_constant(ty))
    }

    fn callee_hole(
        &mut self,
        _cx: &mut Module,
        hole: HoleId,
        _key: &HostKey,
        _args: &[InstArg],
        _sig: &FuncTy,
    ) -> Result<LinkAnswer, HostRefusal> {
        Ok(LinkAnswer::rust(format!("__skolem_hole_{}", hole.index())))
    }

    fn global_hole(
        &mut self,
        _cx: &mut Module,
        hole: HoleId,
        _key: &HostKey,
        _args: &[InstArg],
        _ty: &Ty,
        _mutable: bool,
    ) -> Result<GlobalAnswer, HostRefusal> {
        Ok(GlobalAnswer {
            symbol: format!("__skolem_hole_{}", hole.index()),
            linkage: Linkage::External,
            visibility: Visibility::Default,
            initializer: None,
            align: None,
        })
    }

    fn instance(&mut self, _cx: &mut Module, _sig: &FuncTy) -> Result<InstanceHeader, HostRefusal> {
        Ok(InstanceHeader {
            symbol: SKOLEM_BODY_SYMBOL.to_string(),
            linkage: Linkage::External,
            visibility: Visibility::Default,
            calling_conv: CallingConv::Rust,
            attrs: FuncAttrs::default(),
            display_path: None,
            body_gate: BodyGate::Ungated,
        })
    }

    fn destructor(&mut self, _cx: &mut Module, _ty: &Ty) -> Result<Destructor, HostRefusal> {
        Err(HostRefusal("the skolem instance asks no destructor".into()))
    }

    fn tuple_layout(
        &mut self,
        _cx: &mut Module,
        _ty: &Ty,
    ) -> Result<Option<TupleLayout>, HostRefusal> {
        Ok(None)
    }
}

// ---------------------------------------------------------------------------
// The scripted host (§8): every answer is data
// ---------------------------------------------------------------------------

impl InstantiationHost for ScriptedHost {
    fn arguments(
        &mut self,
        cx: &mut Module,
        _params: &[TemplateParam],
    ) -> Result<Vec<InstArg>, HostRefusal> {
        cx.structs.extend(self.structs.iter().cloned());
        cx.enums.extend(self.enums.iter().cloned());
        cx.types.extend(self.types.iter().cloned());
        if self.tamper {
            cx.name.push_str("_tampered");
        }
        Ok(self.arguments.clone())
    }

    fn type_hole(
        &mut self,
        _cx: &mut Module,
        hole: HoleId,
        _key: &HostKey,
        _args: &[InstArg],
    ) -> Result<Ty, HostRefusal> {
        match self.scripted(hole)? {
            HoleAnswer::Type(ty) => Ok(ty),
            _ => Err(HostRefusal(format!(
                "the script answers ?{} with another kind",
                hole.index()
            ))),
        }
    }

    fn const_hole(
        &mut self,
        _cx: &mut Module,
        hole: HoleId,
        _key: &HostKey,
        _args: &[InstArg],
        _ty: &Ty,
    ) -> Result<Constant, HostRefusal> {
        match self.scripted(hole)? {
            HoleAnswer::Const(value) => Ok(value),
            _ => Err(HostRefusal(format!(
                "the script answers ?{} with another kind",
                hole.index()
            ))),
        }
    }

    fn callee_hole(
        &mut self,
        _cx: &mut Module,
        hole: HoleId,
        _key: &HostKey,
        _args: &[InstArg],
        _sig: &FuncTy,
    ) -> Result<LinkAnswer, HostRefusal> {
        match self.scripted(hole)? {
            HoleAnswer::Callee(answer) => Ok(answer),
            _ => Err(HostRefusal(format!(
                "the script answers ?{} with another kind",
                hole.index()
            ))),
        }
    }

    fn global_hole(
        &mut self,
        _cx: &mut Module,
        hole: HoleId,
        _key: &HostKey,
        _args: &[InstArg],
        _ty: &Ty,
        _mutable: bool,
    ) -> Result<GlobalAnswer, HostRefusal> {
        match self.scripted(hole)? {
            HoleAnswer::Global(answer) => Ok(answer),
            _ => Err(HostRefusal(format!(
                "the script answers ?{} with another kind",
                hole.index()
            ))),
        }
    }

    fn instance(&mut self, _cx: &mut Module, _sig: &FuncTy) -> Result<InstanceHeader, HostRefusal> {
        self.header
            .clone()
            .ok_or_else(|| HostRefusal("the script names no instance header".into()))
    }

    fn destructor(&mut self, _cx: &mut Module, ty: &Ty) -> Result<Destructor, HostRefusal> {
        self.destructors
            .iter()
            .find(|(t, _)| t == ty)
            .map(|(_, answer)| answer.clone())
            .ok_or_else(|| HostRefusal(format!("the script states no destructor of {ty}")))
    }

    fn tuple_layout(
        &mut self,
        _cx: &mut Module,
        ty: &Ty,
    ) -> Result<Option<TupleLayout>, HostRefusal> {
        Ok(self
            .tuple_layouts
            .iter()
            .find(|(t, _)| t == ty)
            .map(|(_, layout)| layout.clone()))
    }
}

trait Scripted {
    fn scripted(&self, hole: HoleId) -> Result<HoleAnswer, HostRefusal>;
}

impl Scripted for ScriptedHost {
    fn scripted(&self, hole: HoleId) -> Result<HoleAnswer, HostRefusal> {
        match self.holes.get(hole.as_usize()) {
            Some(ScriptedAnswer::Answer(answer)) => Ok(answer.clone()),
            Some(ScriptedAnswer::Refuse(why)) => Err(HostRefusal(why.clone())),
            None => Err(HostRefusal(format!(
                "the script does not answer ?{}",
                hole.index()
            ))),
        }
    }
}
