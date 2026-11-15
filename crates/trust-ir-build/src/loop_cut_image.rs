// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Untrusted image assembly for a typed original natural-loop iteration or entry prefix.
//!
//! Only the original instructions and edge arguments are semantic endpoints.
//! The structural cut's synthetic Returns are never read. A concrete, reviewed
//! model supplies instruction meanings and explicit CPS-image proof candidates;
//! this module supplies SSA substitution, control flow and image composition.
//! Close the complete graph in ONE local scope, independently reconstruct its
//! claim, kernel-check it and audit its dependencies before using any result.
//! No provider fidelity, termination, source correspondence or native authority follows.
//! A universally closed image can be alpha-equivalent for different SSA input
//! maps. Consumers must reconstruct those maps from their full original context
//! and instantiate the exact boundary before checking source correspondence.

use crate::{
    ModuleValidationReport,
    cps_image_replay::ImageTypes,
    loop_cut::NaturalLoopCut,
    loop_entry_cut::EntryPrefixCut,
    scoped_local::{ScopedLocal, ScopedLocalAllocator},
    semantic_evaluation::{CPS_IMAGE, CPS_IMAGE_HANDLE, FAIL, HANDLE, TO_CPS},
};
use clean_kernel::{Expr, Level, Name};
use std::collections::BTreeMap;
use trust_ir::{BlockId, FuncId, Function, Inst, InstrNode, Module, Ty, ValueId};

type Result<T> = std::result::Result<T, String>;

fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string(name), vec![Level::zero()]),
        args,
    )
}
fn product(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Prod"),
            vec![Level::zero(), Level::zero()],
        ),
        [a, b],
    )
}
fn lanes(types: &[Expr]) -> Expr {
    types
        .iter()
        .rev()
        .fold(Expr::const_str("Unit"), |tail, ty| {
            product(ty.clone(), tail)
        })
}
fn lams(locals: &[ScopedLocal], body: Expr) -> Expr {
    locals
        .iter()
        .rev()
        .fold(body, |body, local| local.lam(body))
}
fn image(types: &ImageTypes, run: Expr, cps: Expr) -> Expr {
    app(
        CPS_IMAGE,
        [
            types.state.clone(),
            types.error.clone(),
            types.value.clone(),
            types.answer.clone(),
            run,
            cps,
        ],
    )
}
fn cps_type(types: &ImageTypes) -> Expr {
    let channel = |value| {
        Expr::arrow(
            types.state.clone(),
            Expr::arrow(value, types.answer.clone()),
        )
    };
    Expr::arrow(
        types.state.clone(),
        Expr::arrow(
            channel(types.value.clone()),
            Expr::arrow(channel(types.error.clone()), types.answer.clone()),
        ),
    )
}

/// A typed actual SSA value and its interpretation in the caller's local scope.
#[derive(Clone)]
pub struct CutValue {
    pub id: ValueId,
    pub ty: Ty,
    pub term: Expr,
}

/// Exact borrowed site, including annotations and module/callee context.
#[derive(Clone, Copy)]
pub struct CutSite<'m> {
    pub module: &'m Module,
    pub function: &'m Function,
    pub block: BlockId,
    pub instruction: usize,
    pub node: &'m InstrNode,
}

mod entry;
pub use entry::{
    EntryCutImageEndpoint, EntryHeaderArgument, EntryHeaderArrival, EntryHeaderBoundary,
    EntryHeaderEdge,
};

/// A candidate for `CpsImage state error value answer run cps`.
/// Public fields are deliberately untrusted. No Rust wrapper certifies a term.
#[derive(Clone)]
pub struct CutImageCandidate {
    pub run: Expr,
    pub cps: Expr,
    pub proof: Expr,
}
impl CutImageCandidate {
    pub fn proposition(&self, types: &ImageTypes) -> Expr {
        image(types, self.run.clone(), self.cps.clone())
    }
}

/// Semantic TCB extension selected by a concrete consumer, never by proof bytes.
/// Every method must reconstruct deterministically from the actual operands and
/// original module. In particular `instruction` must retain actual call/provider
/// identities, effects and outcomes, with a genuine image premise where needed.
/// The model must interpret or refuse relevant annotations/tables in `original`.
/// A weak or incorrect model cannot be repaired by the image theorem.
pub trait CutImageModel {
    fn original(&self, module: &Module, function: &Function) -> Result<()>;
    fn value_type(&self, module: &Module, ty: &Ty) -> Result<Expr>;
    /// Result value is a right-nested product of ALL result lanes ending in Unit.
    fn instruction<L: ScopedLocalAllocator>(
        &self,
        locals: &mut L,
        site: &CutSite<'_>,
        operands: &[CutValue],
        result_types: &[Expr],
        types: &ImageTypes,
    ) -> Result<CutImageCandidate>;
    /// First arrival at the real header, before any header instruction runs.
    /// Preserve ALL computed header lanes and original captures explicitly in
    /// the model's result. This is not a backedge or a synthetic Return. The
    /// default refuses so iteration-only models retain their current behavior.
    fn entering<L: ScopedLocalAllocator>(
        &self,
        _locals: &mut L,
        _boundary: &EntryHeaderBoundary<'_>,
        _types: &ImageTypes,
    ) -> Result<CutImageCandidate> {
        Err("entry header has no semantic image model".into())
    }
    /// Exact original backedge lanes, in header-parameter order; captures retain
    /// their original SSA IDs, not header aliases or producer correspondence.
    fn continuing<L: ScopedLocalAllocator>(
        &self,
        locals: &mut L,
        site: &CutSite<'_>,
        arguments: &[CutValue],
        captures: &[CutValue],
        types: &ImageTypes,
    ) -> Result<CutImageCandidate>;
    /// Exact actual Return values, including any model-specific failure payload.
    fn returning<L: ScopedLocalAllocator>(
        &self,
        locals: &mut L,
        site: &CutSite<'_>,
        values: &[CutValue],
        types: &ImageTypes,
    ) -> Result<CutImageCandidate>;
}

/// Construction caps only, not aggregate memory, kernel work or machine stack.
#[derive(Clone, Copy)]
pub struct CutImageLimits {
    pub operations: usize,
    pub depth: usize,
    pub lanes: usize,
}
impl Default for CutImageLimits {
    fn default() -> Self {
        Self {
            operations: 65_536,
            depth: 256,
            lanes: 256,
        }
    }
}

/// Original types and identities shared by both independently validated cuts.
struct OriginalEndpoint<'m> {
    module: &'m Module,
    function: &'m Function,
    values: BTreeMap<ValueId, Ty>,
}
impl<'m> OriginalEndpoint<'m> {
    fn new(report: &ModuleValidationReport<'m>, function: FuncId) -> Result<Self> {
        let module = report
            .validated_module()
            .ok_or("cut image requires complete original module validation")?;
        let function = module
            .functions
            .iter()
            .find(|f| f.id == function)
            .ok_or("cut image missing original function")?;
        Ok(Self {
            module,
            function,
            values: BTreeMap::new(),
        })
    }

    // Build the type map only AFTER the selected structural cut has passed its
    // existing block/instruction/cycle guards. Refused cuts never allocate it.
    fn index_values(&mut self) -> Result<()> {
        for block in &self.function.blocks {
            for (id, ty) in &block.params {
                self.values.insert(*id, ty.clone());
            }
            for node in &block.body {
                let types = node.result_tys(self.module);
                if node.results.len() != types.len() {
                    return Err("cut image original result arity".into());
                }
                for (id, ty) in node.results.iter().zip(types) {
                    self.values.insert(*id, ty);
                }
            }
        }
        Ok(())
    }
    fn instantiate(
        &self,
        image: &ParameterizedCutImage<'m>,
        header: BlockId,
        role: ImageRole,
        ids: &[ValueId],
        bindings: &[CutValue],
    ) -> Result<CutImageCandidate> {
        if image.role != role {
            return Err("cut image belongs to a different endpoint role".into());
        }
        if !std::ptr::eq(self.module, image.module)
            || !std::ptr::eq(self.function, image.function)
            || header != image.header
        {
            return Err("cut image belongs to a different original endpoint".into());
        }
        if image.ids != ids
            || image.parameters.len() != ids.len()
            || image.nominal_types.len() != ids.len()
            || bindings.len() != ids.len()
        {
            return Err("cut image changed original boundary map".into());
        }
        let mut supplied = BTreeMap::new();
        for value in bindings {
            if image.parameters.iter().any(|p| p.term() == &value.term) {
                return Err("cut image cannot instantiate a parameter with itself".into());
            }
            if supplied.insert(value.id, value).is_some() {
                return Err("duplicate cut image boundary binding".into());
            }
        }
        let mut arguments = Vec::new();
        for (id, retained) in ids.iter().zip(&image.nominal_types) {
            let value = supplied
                .get(id)
                .ok_or("missing current original boundary binding")?;
            if self.values.get(id) != Some(retained) || value.ty != *retained {
                return Err("cut image boundary nominal type changed".into());
            }
            arguments.push(value.term.clone());
        }
        let instantiate = |term: Expr| Expr::apps(lams(&image.parameters, term), arguments.clone());
        Ok(CutImageCandidate {
            run: instantiate(image.candidate.run.clone()),
            cps: instantiate(image.candidate.cps.clone()),
            proof: instantiate(image.candidate.proof.clone()),
        })
    }
}

/// A borrowed validated ORIGINAL iteration endpoint. The analysis projection is not a body.
pub struct CutImageEndpoint<'m> {
    original: OriginalEndpoint<'m>,
    cut: NaturalLoopCut<'m>,
}
impl<'m> CutImageEndpoint<'m> {
    pub fn new(
        report: &ModuleValidationReport<'m>,
        function: FuncId,
        header: BlockId,
    ) -> Result<Self> {
        let mut original = OriginalEndpoint::new(report, function)?;
        let cut = NaturalLoopCut::new(original.function, header)?;
        original.index_values()?;
        Ok(Self { original, cut })
    }

    /// Parameters are real header lanes followed by original external values.
    /// Both this telescope and the returned candidate belong to `locals`.
    pub fn reconstruct<M: CutImageModel, L: ScopedLocalAllocator>(
        &self,
        model: &M,
        locals: &mut L,
        types: ImageTypes,
        limits: CutImageLimits,
    ) -> Result<ParameterizedCutImage<'m>> {
        if limits.operations == 0 || limits.depth == 0 || limits.lanes == 0 {
            return Err("invalid cut image construction limits".into());
        }
        model.original(self.original.module, self.cut.original())?;
        let header = self
            .cut
            .original()
            .blocks
            .iter()
            .find(|b| b.id == self.cut.header())
            .ok_or("missing cut image header")?;
        let ids = header
            .params
            .iter()
            .map(|(id, _)| *id)
            .chain(self.cut.external_values().iter().copied())
            .collect::<Vec<_>>();
        if ids.len() > limits.lanes {
            return Err("cut image boundary lane limit".into());
        }
        let mut parameters = Vec::new();
        let mut bindings = BTreeMap::new();
        for id in &ids {
            let ty = self
                .original
                .values
                .get(id)
                .ok_or("missing original boundary type")?;
            let local = locals.allocate_local(model.value_type(self.original.module, ty)?)?;
            bindings.insert(*id, local.term().clone());
            parameters.push(local);
        }
        let mut assembly = Assembly {
            original: &self.original,
            region: Region::Iteration(&self.cut),
            model,
            locals,
            types,
            limits,
            operations: 0,
        };
        let candidate = assembly.block(self.cut.header(), bindings, 0)?;
        Ok(ParameterizedCutImage {
            module: self.original.module,
            function: self.cut.original(),
            header: self.cut.header(),
            role: ImageRole::Iteration,
            nominal_types: ids
                .iter()
                .map(|id| self.original.values[id].clone())
                .collect(),
            ids,
            parameters,
            candidate,
            operations: assembly.operations,
        })
    }

    /// Instantiate from the consumer's CURRENT full original SSA context.
    /// Bindings are keyed by original ID, not supplied position. This checks
    /// borrow/header/nominal-map custody only; their expression meanings/types
    /// still require independent reconstruction and whole-claim kernel replay.
    /// The caller must supply expressions from the same local owner, with
    /// context locals distinct from this fresh image-parameter telescope. Raw
    /// expressions do not authenticate owner/age or their SSA meaning here.
    /// Full expression closure, freshness and source fidelity remain external
    /// replay obligations, even after these nominal checks succeed.
    pub fn at_boundary(
        &self,
        image: &ParameterizedCutImage<'m>,
        bindings: &[CutValue],
    ) -> Result<CutImageCandidate> {
        let header = self
            .cut
            .original()
            .blocks
            .iter()
            .find(|b| b.id == self.cut.header())
            .ok_or("missing original boundary header")?;
        let ids = header
            .params
            .iter()
            .map(|(id, _)| *id)
            .chain(self.cut.external_values().iter().copied())
            .collect::<Vec<_>>();
        self.original.instantiate(
            image,
            self.cut.header(),
            ImageRole::Iteration,
            &ids,
            bindings,
        )
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ImageRole {
    Iteration,
    Entry,
}

/// An iteration telescope contains header lanes/captures; an entry telescope
/// contains only actual entry parameters. The universal image proposition does
/// NOT authenticate these IDs. Use the matching endpoint's nominal helper and
/// independently reconstruct/replay the complete source context.
pub struct ParameterizedCutImage<'m> {
    pub ids: Vec<ValueId>,
    pub parameters: Vec<ScopedLocal>,
    pub candidate: CutImageCandidate,
    pub operations: usize,
    module: &'m Module,
    function: &'m Function,
    header: BlockId,
    nominal_types: Vec<Ty>,
    role: ImageRole,
}

enum Region<'a, 'm> {
    Iteration(&'a NaturalLoopCut<'m>),
    Entry(&'a EntryPrefixCut<'m>),
}
impl Region<'_, '_> {
    fn header(&self) -> BlockId {
        match self {
            Self::Iteration(c) => c.header(),
            Self::Entry(c) => c.header(),
        }
    }
    fn blocks(&self) -> &[BlockId] {
        match self {
            Self::Iteration(c) => c.topological_blocks(),
            Self::Entry(c) => c.topological_blocks(),
        }
    }
    fn captures(&self) -> &[ValueId] {
        match self {
            Self::Iteration(c) => c.external_values(),
            Self::Entry(c) => c.boundary_captures(),
        }
    }
}

struct Assembly<'a, 'm, M, L> {
    original: &'a OriginalEndpoint<'m>,
    region: Region<'a, 'm>,
    model: &'a M,
    locals: &'a mut L,
    types: ImageTypes,
    limits: CutImageLimits,
    operations: usize,
}
impl<'a, 'm, M: CutImageModel, L: ScopedLocalAllocator> Assembly<'a, 'm, M, L> {
    fn spend(&mut self, depth: usize) -> Result<()> {
        self.operations = self
            .operations
            .checked_add(1)
            .ok_or("cut image operation overflow")?;
        if self.operations > self.limits.operations || depth > self.limits.depth {
            return Err("cut image construction limit".into());
        }
        Ok(())
    }
    fn read(&self, bindings: &BTreeMap<ValueId, Expr>, id: ValueId) -> Result<CutValue> {
        Ok(CutValue {
            id,
            ty: self
                .original
                .values
                .get(&id)
                .ok_or("cut image missing original SSA type")?
                .clone(),
            term: bindings
                .get(&id)
                .ok_or("cut image missing dominating SSA value")?
                .clone(),
        })
    }
    fn block(
        &mut self,
        id: BlockId,
        bindings: BTreeMap<ValueId, Expr>,
        depth: usize,
    ) -> Result<CutImageCandidate> {
        self.spend(depth)?;
        if !self.region.blocks().contains(&id) {
            return Err("cut image edge outside original iteration".into());
        }
        self.body(id, 0, bindings, depth + 1)
    }
    fn edge(
        &mut self,
        site: &CutSite<'m>,
        target: BlockId,
        args: &[ValueId],
        arm: EntryHeaderEdge,
        mut bindings: BTreeMap<ValueId, Expr>,
        depth: usize,
    ) -> Result<CutImageCandidate> {
        self.spend(depth)?;
        let arguments = args
            .iter()
            .map(|id| self.read(&bindings, *id))
            .collect::<Result<Vec<_>>>()?;
        if target == self.region.header() {
            if matches!(self.region, Region::Entry(_)) {
                return self.enter_header(
                    EntryHeaderArrival::Edge { site: *site, arm },
                    arguments,
                    &bindings,
                );
            }
            let Region::Iteration(cut) = &self.region else {
                unreachable!()
            };
            let owned = cut
                .backedges()
                .iter()
                .any(|e| e.predecessor == site.block && e.header == target && e.arguments == args);
            if !owned {
                return Err("cut image changed original backedge arguments".into());
            }
            let captures = self
                .region
                .captures()
                .iter()
                .map(|id| self.read(&bindings, *id))
                .collect::<Result<Vec<_>>>()?;
            return self
                .model
                .continuing(self.locals, site, &arguments, &captures, &self.types);
        }
        let block = self
            .original
            .function
            .blocks
            .iter()
            .find(|b| b.id == target)
            .ok_or("cut image missing actual successor")?;
        if block.params.len() != arguments.len() {
            return Err("cut image edge arity".into());
        }
        // Resolve every old argument BEFORE rebinding any successor parameter.
        for ((id, ty), value) in block.params.iter().zip(arguments) {
            if *ty != value.ty {
                return Err("cut image edge nominal type".into());
            }
            bindings.insert(*id, value.term);
        }
        self.block(target, bindings, depth + 1)
    }
    fn body(
        &mut self,
        block: BlockId,
        index: usize,
        mut bindings: BTreeMap<ValueId, Expr>,
        depth: usize,
    ) -> Result<CutImageCandidate> {
        self.spend(depth)?;
        let original = self.original.function;
        let node = original
            .blocks
            .iter()
            .find(|b| b.id == block)
            .and_then(|b| b.body.get(index))
            .ok_or("cut image empty original instruction")?;
        let site = CutSite {
            module: self.original.module,
            function: original,
            block,
            instruction: index,
            node,
        };
        match &node.inst {
            Inst::Return { values } => {
                let values = values
                    .iter()
                    .map(|id| self.read(&bindings, *id))
                    .collect::<Result<Vec<_>>>()?;
                self.model
                    .returning(self.locals, &site, &values, &self.types)
            }
            Inst::Br { target, args } => self.edge(
                &site,
                *target,
                args,
                EntryHeaderEdge::Unconditional,
                bindings,
                depth + 1,
            ),
            Inst::CondBr {
                cond,
                then_target,
                then_args,
                else_target,
                else_args,
            } => {
                let condition = self.read(&bindings, *cond)?;
                if condition.ty != Ty::Bool
                    || self.model.value_type(site.module, &condition.ty)? != Expr::const_str("Bool")
                {
                    return Err("cut image requires exact Boolean branch meaning".into());
                }
                let yes = self.edge(
                    &site,
                    *then_target,
                    then_args,
                    EntryHeaderEdge::Then,
                    bindings.clone(),
                    depth + 1,
                )?;
                let no = self.edge(
                    &site,
                    *else_target,
                    else_args,
                    EntryHeaderEdge::Else,
                    bindings,
                    depth + 1,
                )?;
                self.branch(condition.term, yes, no)
            }
            inst if inst.is_terminator() => Err("cut image unsupported original terminator".into()),
            _ => {
                let ir_types = node.result_tys(site.module);
                if ir_types.len() > self.limits.lanes {
                    return Err("cut image instruction lane limit".into());
                }
                let result_types = ir_types
                    .iter()
                    .map(|ty| self.model.value_type(site.module, ty))
                    .collect::<Result<Vec<_>>>()?;
                let mut operands = Vec::new();
                let mut error = None;
                node.inst
                    .visit_value_operands(|id| match self.read(&bindings, id) {
                        Ok(value) => operands.push(value),
                        Err(e) => error = Some(e),
                    });
                if let Some(e) = error {
                    return Err(e);
                }
                let primitive = self.model.instruction(
                    self.locals,
                    &site,
                    &operands,
                    &result_types,
                    &self.types,
                )?;
                let mut results = Vec::new();
                for (id, ty) in node.results.iter().zip(&result_types) {
                    let local = self.locals.allocate_local(ty.clone())?;
                    bindings.insert(*id, local.term().clone());
                    results.push(local);
                }
                let suffix = self.body(block, index + 1, bindings, depth + 1)?;
                self.sequence(primitive, &result_types, &results, suffix)
            }
        }
    }
    fn branch(
        &mut self,
        flag: Expr,
        yes: CutImageCandidate,
        no: CutImageCandidate,
    ) -> Result<CutImageCandidate> {
        let choose = |ty: Expr, no: Expr, yes: Expr, flag: Expr| {
            Expr::apps(
                Expr::const_(
                    Name::from_string("Bool.rec"),
                    vec![Level::succ(Level::zero())],
                ),
                [
                    Expr::lam(
                        clean_kernel::BinderInfo::Default,
                        Expr::const_str("Bool"),
                        ty.lift(1),
                    ),
                    no,
                    yes,
                    flag,
                ],
            )
        };
        let run_ty = app(
            crate::semantic_evaluation::RUN,
            [
                self.types.state.clone(),
                self.types.error.clone(),
                self.types.value.clone(),
            ],
        );
        let run = choose(
            run_ty.clone(),
            no.run.clone(),
            yes.run.clone(),
            flag.clone(),
        );
        let cps = choose(
            cps_type(&self.types),
            no.cps.clone(),
            yes.cps.clone(),
            flag.clone(),
        );
        let b = self.locals.allocate_local(Expr::const_str("Bool"))?;
        let motive = b.lam(image(
            &self.types,
            choose(run_ty, no.run, yes.run, b.term().clone()),
            choose(cps_type(&self.types), no.cps, yes.cps, b.term().clone()),
        ));
        let proof = Expr::apps(
            Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
            [motive, no.proof, yes.proof, flag],
        );
        Ok(CutImageCandidate { run, cps, proof })
    }
    fn sequence(
        &mut self,
        primitive: CutImageCandidate,
        types: &[Expr],
        results: &[ScopedLocal],
        suffix: CutImageCandidate,
    ) -> Result<CutImageCandidate> {
        let packed = self.locals.allocate_local(lanes(types))?;
        let bind = |body: Expr| {
            let mut projections = Vec::new();
            let mut value = packed.term().clone();
            for (index, ty) in types.iter().enumerate() {
                let tail = lanes(&types[index + 1..]);
                let project = |name| {
                    Expr::apps(
                        Expr::const_(Name::from_string(name), vec![Level::zero(), Level::zero()]),
                        [ty.clone(), tail.clone(), value.clone()],
                    )
                };
                projections.push(project("Prod.fst"));
                value = project("Prod.snd");
            }
            results
                .iter()
                .zip(projections)
                .rev()
                .fold(body, |body, (local, value)| local.let_(value, body))
        };
        let yes = packed.lam(bind(suffix.run));
        let ky = packed.lam(bind(suffix.cps));
        let hy = packed.lam(bind(suffix.proof));
        let failure = self.locals.allocate_local(self.types.error.clone())?;
        let failed_run = app(
            FAIL,
            [
                self.types.state.clone(),
                self.types.error.clone(),
                self.types.value.clone(),
                failure.term().clone(),
            ],
        );
        let no = failure.lam(failed_run.clone());
        let failed_cps = app(
            TO_CPS,
            [
                self.types.state.clone(),
                self.types.error.clone(),
                self.types.value.clone(),
                self.types.answer.clone(),
                failed_run,
            ],
        );
        let kn = failure.lam(failed_cps.clone());
        // The failure-image telescope is retained INSIDE the eventual outer
        // image proof. It must own different locals from that outer telescope.
        let failure_state = self.locals.allocate_local(self.types.state.clone())?;
        let failure_ok = self.locals.allocate_local(Expr::arrow(
            self.types.state.clone(),
            Expr::arrow(self.types.value.clone(), self.types.answer.clone()),
        ))?;
        let failure_err = self.locals.allocate_local(Expr::arrow(
            self.types.state.clone(),
            Expr::arrow(self.types.error.clone(), self.types.answer.clone()),
        ))?;
        let failed_observation = Expr::apps(
            failed_cps,
            [
                failure_state.term().clone(),
                failure_ok.term().clone(),
                failure_err.term().clone(),
            ],
        );
        let hn = failure.lam(lams(
            &[failure_state, failure_ok, failure_err],
            Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.refl"),
                    vec![Level::succ(Level::zero())],
                ),
                [self.types.answer.clone(), failed_observation],
            ),
        ));
        let state = self.locals.allocate_local(self.types.state.clone())?;
        let ok = self.locals.allocate_local(Expr::arrow(
            self.types.state.clone(),
            Expr::arrow(self.types.value.clone(), self.types.answer.clone()),
        ))?;
        let err = self.locals.allocate_local(Expr::arrow(
            self.types.state.clone(),
            Expr::arrow(self.types.error.clone(), self.types.answer.clone()),
        ))?;
        let next = self.locals.allocate_local(self.types.state.clone())?;
        let pty = lanes(types);
        // `ky` already binds `packed`; nesting it underneath a lambda binding
        // that same named ID would violate complete-graph scope ownership.
        let argument = self.locals.allocate_local(pty.clone())?;
        let success = lams(
            &[next.clone(), argument.clone()],
            Expr::apps(
                ky.clone(),
                [
                    argument.term().clone(),
                    next.term().clone(),
                    ok.term().clone(),
                    err.term().clone(),
                ],
            ),
        );
        let run = app(
            HANDLE,
            [
                self.types.state.clone(),
                self.types.error.clone(),
                pty.clone(),
                self.types.error.clone(),
                self.types.value.clone(),
                primitive.run.clone(),
                yes.clone(),
                no.clone(),
            ],
        );
        let cps = lams(
            &[state.clone(), ok.clone(), err.clone()],
            Expr::apps(
                primitive.cps.clone(),
                [state.term().clone(), success, err.term().clone()],
            ),
        );
        let proof = lams(
            &[state.clone(), ok.clone(), err.clone()],
            app(
                CPS_IMAGE_HANDLE,
                [
                    self.types.state.clone(),
                    self.types.error.clone(),
                    pty,
                    self.types.error.clone(),
                    self.types.value.clone(),
                    self.types.answer.clone(),
                    primitive.run,
                    primitive.cps,
                    yes,
                    no,
                    ky,
                    kn,
                    primitive.proof,
                    hy,
                    hn,
                    state.term().clone(),
                    ok.term().clone(),
                    err.term().clone(),
                ],
            ),
        );
        Ok(CutImageCandidate { run, cps, proof })
    }
}

#[cfg(test)]
mod tests;
