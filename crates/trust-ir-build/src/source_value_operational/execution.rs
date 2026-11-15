use super::body::{Word, both, fits};
use super::*;

#[derive(Clone)]
pub(super) struct Inputs {
    pub model: MachineModel,
    pub memory: Expr,
    pub host: Expr,
    pub fuel: Expr,
}
impl Inputs {
    pub fn owner(&self) -> Expr {
        app("ir_byte_fresh_owner_v1", [self.memory.clone()])
    }
    pub fn world(&self) -> Expr {
        app(
            "IRByteWorldV1.mk",
            [
                self.model.world_type().clone(),
                self.memory.clone(),
                self.host.clone(),
                list("Nat", [self.owner()]),
                app("Nat.succ", [self.owner()]),
            ],
        )
    }
    pub fn memory_guard(&self) -> Expr {
        EntryTarget::memory_admission(self.memory.clone())
    }
    pub fn halted(&self, outcome: Expr, world: Expr) -> Expr {
        app(
            "IRByteConfigV1.halted",
            [self.model.world_type().clone(), outcome, world],
        )
    }
    pub fn bad(&self, fault: &str) -> Expr {
        self.halted(app("IROutcome.type_error", [c(fault)]), self.world())
    }
    pub fn run(&self, fuel: Expr, initial: Expr) -> Expr {
        app(
            "ir_byte_run_v1",
            [
                self.model.world_type().clone(),
                self.model.context().clone(),
                self.model.providers().clone(),
                fuel,
                initial,
            ],
        )
    }
    pub fn initial(&self, subject: &Subject<'_>, arguments: Expr) -> Expr {
        app(
            "ir_byte_init_v1",
            [
                self.model.world_type().clone(),
                self.model.context().clone(),
                nat(u64::from(subject.source.function().id.index())),
                arguments,
                self.memory.clone(),
                self.host.clone(),
            ],
        )
    }
    pub fn current(&self, subject: &Subject<'_>, arguments: Expr) -> Current {
        Current {
            frame: app(
                "IRFrame.mk",
                [
                    nat(u64::from(subject.source.function().id.index())),
                    nat(u64::from(subject.source.function().entry.index())),
                    nat(0),
                    app(
                        "ir_bind_params",
                        [
                            list(
                                "Nat",
                                subject.parameters.map(|id| nat(u64::from(id.index()))),
                            ),
                            arguments,
                            list("IRBinding", []),
                        ],
                    ),
                    list("Nat", []),
                ],
            ),
            tail: list("IRFrame", []),
            legacy_memory: list("IRMemSlot", []),
            legacy_cursor: nat(0),
            world: self.world(),
        }
    }
    pub fn returned(&self, value: Expr) -> Expr {
        let world = app(
            "IRByteWorldV1.mk",
            [
                self.model.world_type().clone(),
                app("ir_byte_retire_v1", [self.owner(), self.memory.clone()]),
                self.host.clone(),
                list("Nat", []),
                app("Nat.succ", [self.owner()]),
            ],
        );
        self.halted(
            app("IROutcome.ret", [list("IRScalar", [int(value)])]),
            world,
        )
    }
}

pub(super) fn states(subject: &Subject<'_>, input: &Inputs, x: Expr, y: Expr) -> Vec<Expr> {
    let mut current = input.current(subject, list("IRScalar", [int(x.clone()), int(y.clone())]));
    let mut result = vec![current.running(&input.model)];
    let mut values = BTreeMap::from([
        (subject.parameters[0], x.clone()),
        (subject.parameters[1], y.clone()),
    ]);
    for operation in &subject.operations {
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
                subject
                    .profile
                    .actual_word(*kind, values[left].clone(), values[right].clone()),
            ),
        };
        current.frame = app(
            "ir_frame_advance",
            [app(
                "ir_frame_set_many",
                [
                    current.frame,
                    list("Nat", [nat(u64::from(id.index()))]),
                    list("IRScalar", [int(value.clone())]),
                ],
            )],
        );
        values.insert(id, value);
        result.push(current.running(&input.model));
    }
    result.push(input.returned(subject.denotation(x, y)));
    result
}

// A finite prefix lookup, with the final halted value for every larger fuel.
// This does not manufacture an OutOfFuel outcome for a partial running state.
pub(super) fn select(fuel: Expr, states: &[Expr], ty: Expr) -> Expr {
    if states.len() == 1 {
        return states[0].clone();
    }
    let n = Expr::bvar(1);
    // The two binders are predecessor and the unused recursive result.
    let tail = select(n, &states[1..], ty.clone());
    Expr::apps(
        Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            Expr::lam(BinderInfo::Default, c("Nat"), ty.clone()),
            states[0].clone(),
            Expr::lam(
                BinderInfo::Default,
                c("Nat"),
                Expr::lam(BinderInfo::Default, ty, tail),
            ),
            fuel,
        ],
    )
}

// One scalar chain, all premises derived from the two input canonical bounds
// and actual initialization. No operation answer or run-success hypothesis.
pub(super) fn successful(
    subject: &Subject<'_>,
    environment: &Environment,
    assembler: &mut Assembler<'_>,
    input: &Inputs,
    x: Expr,
    y: Expr,
    hx: PendingProof,
    hy: PendingProof,
    memory: PendingEquality,
) -> Result<(Vec<Expr>, Vec<PendingEquality>)> {
    let model = &input.model;
    let mut catalog = Catalog::new(environment, &subject.reflected, subject.limits)?;
    let entry = catalog.entry(subject.source.function().id)?;
    let target = catalog.call_target(subject.source.function().id)?;
    let arguments = list("IRScalar", [int(x.clone()), int(y.clone())]);
    let words = BTreeMap::from([
        (
            subject.parameters[0],
            Word {
                value: x.clone(),
                bound: hx,
                denotation: x.clone(),
                equation: pending(c("Nat"), x.clone()),
            },
        ),
        (
            subject.parameters[1],
            Word {
                value: y.clone(),
                bound: hy,
                denotation: y.clone(),
                equation: pending(c("Nat"), y.clone()),
            },
        ),
    ]);
    let xfits = fits(
        subject.profile,
        assembler,
        model,
        &words[&subject.parameters[0]],
    )?;
    let yfits = fits(
        subject.profile,
        assembler,
        model,
        &words[&subject.parameters[1]],
    )?;
    let ylist = both(assembler, yfits, pending(c("Bool"), c("Bool.true")))?;
    let admitted = both(assembler, xfits, ylist)?;
    let admitted = assembler.convert_endpoints(
        admitted,
        entry.admission(model, arguments.clone())?,
        c("Bool.true"),
    )?;
    let initialized = entry.initialize(
        assembler,
        model,
        arguments,
        input.memory.clone(),
        input.host.clone(),
        memory,
        admitted,
    )?;
    let current = input.current(subject, list("IRScalar", [int(x.clone()), int(y.clone())]));
    let initialized_equation = assembler.convert_endpoints(
        initialized.equality().clone(),
        initialized.equality().left().clone(),
        current.running(model),
    )?;
    let validity = assembler.convert_endpoints(
        initialized.valid().clone(),
        current.valid(model),
        c("Bool.true"),
    )?;
    let body = super::body::derive(
        subject,
        assembler,
        &mut catalog,
        model,
        current,
        validity,
        words,
    )?;
    let mut all_states = body.states;
    let mut steps = body.steps;
    let current = body.current;
    let validity = body.valid;
    let word = &body.result;
    let returning = catalog.fetch(Coordinate {
        function: subject.source.function().id,
        block: subject.source.function().entry,
        instruction: subject.operations.len(),
    })?;
    let frame = RootReturnFrame {
        returning: current.frame.clone(),
        legacy_memory: current.legacy_memory.clone(),
        legacy_cursor: current.legacy_cursor.clone(),
        memory: input.memory.clone(),
        host: input.host.clone(),
        owner: input.owner(),
        next: app("Nat.succ", [input.owner()]),
    };
    let values = list("IRScalar", [int(word.value.clone())]);
    let resolved = assembler.conversion(
        app("IRList", [c("IRScalar")]),
        app(
            "ir_resolve",
            [
                current.machine(),
                list("Nat", [nat(u64::from(subject.returned.index()))]),
            ],
        ),
        values.clone(),
    )?;
    let fit = fits(subject.profile, assembler, model, word)?;
    let fit = both(assembler, fit, pending(c("Bool"), c("Bool.true")))?;
    let fit = both(assembler, fit, pending(c("Bool"), c("Bool.true")))?;
    let admitted = assembler.convert_endpoints(
        fit,
        returning.root_return_admission(model, &target, &frame, values)?,
        c("Bool.true"),
    )?;
    let returned = returning.return_from_root(
        assembler, model, &target, &frame, resolved, admitted, validity,
    )?;
    let final_map = mapped(
        assembler,
        symm(&word.equation),
        model.config_type(),
        |value| input.returned(value),
    )?;
    let one = assembler.compose(returned.run().equality().clone(), final_map)?;
    // return_from_root exports run-one; a running head makes it exactly step.
    let one = assembler.convert_endpoints(
        one,
        model.step(current.running(model)),
        input.returned(word.denotation.clone()),
    )?;
    steps.push(one);
    all_states.push(input.returned(word.denotation.clone()));
    let expected = states(subject, input, x, y);
    if all_states != expected {
        return Err("operational prefix reconstruction disagrees".into());
    }
    // Initialization equality is prepended for the caller, not a fuel step.
    let mut equations = vec![initialized_equation];
    equations.extend(steps);
    Ok((all_states, equations))
}

pub(super) fn run_prefix(
    assembler: &mut Assembler<'_>,
    input: &Inputs,
    fuel: Expr,
    states: &[Expr],
    steps: &[PendingEquality],
) -> Result<PendingEquality> {
    let ty = input.model.config_type();
    let left = input.run(fuel.clone(), states[0].clone());
    let right = select(fuel.clone(), states, ty.clone());
    if states.len() == 1 {
        let args = states[0].get_app_args();
        return Ok(PendingEquality::candidate(
            ty,
            left,
            right,
            app(
                "ir_byte_run_halted_v1",
                [
                    input.model.world_type().clone(),
                    input.model.context().clone(),
                    input.model.providers().clone(),
                    args[1].clone(),
                    args[2].clone(),
                    fuel,
                ],
            ),
        ));
    }
    let n = assembler.local(c("Nat"))?;
    let predecessor = run_prefix(
        assembler,
        input,
        n.term().clone(),
        &states[1..],
        &steps[1..],
    )?;
    let mapped = mapped(assembler, steps[0].clone(), ty.clone(), |state| {
        input.run(n.term().clone(), state)
    })?;
    let next = assembler.compose(mapped, predecessor)?;
    let next = assembler.convert_endpoints(
        next,
        input.run(app("Nat.succ", [n.term().clone()]), states[0].clone()),
        select(app("Nat.succ", [n.term().clone()]), states, ty.clone()),
    )?;
    let k = assembler.local(c("Nat"))?;
    let motive = k.lam(eq(
        ty.clone(),
        input.run(k.term().clone(), states[0].clone()),
        select(k.term().clone(), states, ty.clone()),
    ));
    let ih = assembler.local(eq(
        ty.clone(),
        input.run(n.term().clone(), states[0].clone()),
        select(n.term().clone(), states, ty.clone()),
    ))?;
    let base = app("Eq.refl", [ty.clone(), states[0].clone()]);
    let proof = Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
        [motive, base, n.lam(ih.lam(next.term().clone())), fuel],
    );
    Ok(PendingEquality::candidate(ty, left, right, proof))
}
