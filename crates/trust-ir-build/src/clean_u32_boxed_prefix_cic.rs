// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Checked, invocation-specific four-node prefix mathematics for the SAME
//! original admitted module. This target is explicitly distinct from ByteV1.
//!
//! The claim retains the entire initialized ByteConfig, memory, Nat host,
//! activation owners/next, two occurrence flags and remaining node budget.
//! It stops RUNNING at the actual scalar-call site; it neither invokes scalar
//! root mathematics in a caller frame nor proves the complete boxed helper.
//! The source/reflection mapper and five runtime-source associations remain
//! explicit TCB. No universal refinement of the Rust prefix/UInt32Heap, native
//! import, ARC, ABI, body permission or successful default ByteV1 is asserted.
//! In particular this API accepts a defined Byte-world projection, NOT an
//! owned Rust heap whose allocations or ghost frames could be silently erased.

use std::collections::BTreeMap;

use clean_kernel::{BinderInfo, Environment, Expr, Level, Name};
use trust_ir::clean_boxed_u32::RuntimeSources;
use trust_ir::{FuncId, ValueId};

use crate::clean_u32_boxed_prefix::prepare_tagged_u32_boxed_prefix;

pub(crate) mod universal;
use crate::source_value_operational::{
    CheckedSourceValueOperational, import_source_closure, strict_replay,
};

/// One actual byte allocation in the explicit mathematical projection. Owner0
/// denotes caller-owned live memory; other live owners fail canonical entry
/// admission. Dead historical allocations remain present and affect fresh IDs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrefixAllocation {
    pub base: u64,
    pub size: u64,
    pub owner: u64,
    pub live: bool,
}

/// Complete finite Byte-memory map and Nat host for this fixed profile.
/// Missing byte addresses are genuinely undefined. These values are not a
/// representation theorem for a Rust heap or native addresses.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PrefixWorld {
    pub allocations: Vec<PrefixAllocation>,
    pub bytes: BTreeMap<u64, u8>,
    pub next_address: u64,
    pub host: u64,
}

#[derive(Debug)]
pub enum PrefixCicError {
    Subject(String),
    TaggedDomain,
    Bounds,
    Replay(String),
}
impl core::fmt::Display for PrefixCicError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "checked tagged-prefix refusal: {self:?}")
    }
}
impl std::error::Error for PrefixCicError {}

/// Immutable association with the original receipt; the endpoint was derived
/// independently from its original wrapper, then checked strict/rooted/noAX
/// and through lossless DAG replay. Only the NEW named CIC target is certified.
pub struct CheckedTaggedPrefixCic<'receipt, 'source> {
    source: &'receipt CheckedSourceValueOperational<'source>,
    wrapper: FuncId,
    environment: Environment,
    claim: Expr,
    proof: Expr,
    initial: Expr,
    endpoint: Expr,
    consumed: u64,
    remaining: u64,
}
impl<'source> CheckedTaggedPrefixCic<'_, 'source> {
    pub fn source(&self) -> &CheckedSourceValueOperational<'source> {
        self.source
    }
    pub fn wrapper(&self) -> FuncId {
        self.wrapper
    }
    pub fn environment(&self) -> &Environment {
        &self.environment
    }
    pub fn claim(&self) -> &Expr {
        &self.claim
    }
    pub fn proof(&self) -> &Expr {
        &self.proof
    }
    pub fn initial(&self) -> &Expr {
        &self.initial
    }
    pub fn endpoint(&self) -> &Expr {
        &self.endpoint
    }
    pub fn consumed(&self) -> u64 {
        self.consumed
    }
    pub fn remaining(&self) -> u64 {
        self.remaining
    }
}

fn c(name: &str) -> Expr {
    let levels = if name == "Bool.rec" {
        vec![Level::succ(Level::zero())]
    } else {
        vec![]
    };
    Expr::const_(Name::from_string(name), levels)
}
fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}
fn nat(n: u64) -> Expr {
    Expr::nat_lit(n)
}
fn boolean(b: bool) -> Expr {
    c(if b { "Bool.true" } else { "Bool.false" })
}
fn list(ty: &str, xs: impl IntoIterator<Item = Expr>) -> Expr {
    xs.into_iter()
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .fold(app("IRList.nil", [c(ty)]), |tail, head| {
            app("IRList.cons", [c(ty), head, tail])
        })
}
fn binding(id: ValueId, value: Expr) -> Expr {
    app("IRBinding.mk", [nat(u64::from(id.index())), value])
}
fn memory(world: &PrefixWorld) -> Expr {
    let address = Expr::bvar(0);
    let bytes =
        world
            .bytes
            .iter()
            .fold(app("IROption.none", [c("Nat")]), |rest, (&key, &value)| {
                app(
                    "Bool.rec",
                    [
                        Expr::lam(BinderInfo::Default, c("Bool"), app("IROption", [c("Nat")])),
                        rest,
                        app("IROption.some", [c("Nat"), nat(u64::from(value))]),
                        app("ir_nat_eqb", [address.clone(), nat(key)]),
                    ],
                )
            });
    app(
        "IRByteMemoryV1.mk",
        [
            list(
                "IRByteAllocationV1",
                world.allocations.iter().map(|a| {
                    app(
                        "IRByteAllocationV1.mk",
                        [nat(a.base), nat(a.size), nat(a.owner), boolean(a.live)],
                    )
                }),
            ),
            Expr::lam(BinderInfo::Default, c("Nat"), bytes),
            nat(world.next_address),
        ],
    )
}

fn checked_environment(
    source: &CheckedSourceValueOperational<'_>,
) -> Result<Environment, PrefixCicError> {
    let mut environment =
        clean_verify::eval_ir_tagged_u32_prefix::build_tagged_u32_prefix_spec_v1_with_stack()
            .map_err(|e| PrefixCicError::Replay(e.to_string()))?
            .into_environment();
    import_source_closure(
        &mut environment,
        source.source_value().environment(),
        source.source_value(),
    )
    .map_err(PrefixCicError::Replay)?;
    if environment
        .closure_digest(source.source_value().source())
        .map_err(|e| PrefixCicError::Replay(e.to_string()))?
        != *source.source_value().source_closure_digest()
    {
        return Err(PrefixCicError::Subject("source closure changed".into()));
    }
    Ok(environment)
}

/// Prove a bounded initialized prefix against the original complete reflected
/// context. There is no provider argument, arbitrary context term or caller
/// environment. All signature/graph/source identities come from the original
/// private checked receipt and the existing source-bound wrapper preparation.
/// The node budget is this target's budget, not ByteV1 fuel or native cost.
pub fn check_tagged_u32_boxed_prefix_execution<'receipt, 'source>(
    source: &'receipt CheckedSourceValueOperational<'source>,
    wrapper: FuncId,
    runtime_sources: &RuntimeSources<'_>,
    words: [u64; 2],
    node_budget: u64,
    world: &PrefixWorld,
) -> Result<CheckedTaggedPrefixCic<'receipt, 'source>, PrefixCicError> {
    runtime_sources
        .bind()
        .map_err(|e| PrefixCicError::Subject(format!("{e:?}")))?;
    let prepared = prepare_tagged_u32_boxed_prefix(source, wrapper)
        .map_err(|e| PrefixCicError::Subject(e.to_string()))?;
    if words
        .iter()
        .any(|word| word & 1 != 1 || word / 2 > u64::from(u32::MAX))
    {
        return Err(PrefixCicError::TaggedDomain);
    }
    if node_budget > 64 || world.allocations.len() > 64 || world.bytes.len() > 256 {
        return Err(PrefixCicError::Bounds);
    }
    let owner = world
        .allocations
        .iter()
        .map(|a| a.owner)
        .max()
        .unwrap_or(0)
        .checked_add(1)
        .ok_or(PrefixCicError::Bounds)?;
    let next = owner.checked_add(1).ok_or(PrefixCicError::Bounds)?;
    let body = &prepared.wrapper().blocks[0];
    let [a, b] = body.params.as_slice() else {
        return Err(PrefixCicError::Bounds);
    };
    let parameters = [a.0, b.0];
    let decoded = [body.body[0].results[0], body.body[1].results[0]];
    let environment = checked_environment(source)?;
    let mem = memory(world);
    let initial = app(
        "ir_clean_tag32_init_v1",
        [
            c("Nat"),
            source.context().clone(),
            nat(u64::from(wrapper.index())),
            list(
                "IRScalar",
                words.map(|word| app("IRScalar.ptr_", [nat(word)])),
            ),
            mem.clone(),
            nat(world.host),
        ],
    );
    // Independently reconstruct the exact endpoint, without normalizing or
    // reading the target driver's result. Original parameter/results IDs remain.
    let consumed = node_budget.min(4);
    let remaining = node_budget - consumed;
    let mut locals = vec![
        binding(parameters[0], app("IRScalar.ptr_", [nat(words[0])])),
        binding(parameters[1], app("IRScalar.ptr_", [nat(words[1])])),
    ];
    for i in 0..usize::try_from(consumed.min(2)).map_err(|_| PrefixCicError::Bounds)? {
        locals.insert(
            0,
            binding(decoded[i], app("IRScalar.int_", [nat(words[i] / 2)])),
        );
    }
    let frame = app(
        "IRFrame.mk",
        [
            nat(u64::from(wrapper.index())),
            nat(u64::from(body.id.index())),
            nat(consumed),
            list("IRBinding", locals),
            list("Nat", []),
        ],
    );
    let machine = app(
        "IRMachine.mk",
        [list("IRFrame", [frame]), list("IRMemSlot", []), nat(0)],
    );
    let final_world = app(
        "IRByteWorldV1.mk",
        [
            c("Nat"),
            mem,
            nat(world.host),
            list("Nat", [nat(owner)]),
            nat(next),
        ],
    );
    let endpoint = app(
        "IRCleanTag32RunV1.mk",
        [
            c("Nat"),
            app(
                "IRCleanTag32PrefixV1.mk",
                [
                    c("Nat"),
                    app("IRByteConfigV1.running", [c("Nat"), machine, final_world]),
                    boolean(consumed < 3),
                    boolean(consumed < 4),
                ],
            ),
            nat(remaining),
        ],
    );
    let actual = app(
        "ir_clean_tag32_run_v1",
        [
            c("Nat"),
            source.context().clone(),
            nat(u64::from(wrapper.index())),
            nat(u64::from(body.id.index())),
            nat(u64::from(prepared.unbox_id().index())),
            nat(u64::from(parameters[0].index())),
            nat(u64::from(parameters[1].index())),
            nat(node_budget),
            initial.clone(),
        ],
    );
    let ty = app("IRCleanTag32RunV1", [c("Nat")]);
    let claim = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty.clone(), actual, endpoint.clone()],
    );
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, endpoint.clone()],
    );
    strict_replay(&environment, &claim, &proof).map_err(PrefixCicError::Replay)?;
    Ok(CheckedTaggedPrefixCic {
        source,
        wrapper,
        environment,
        claim,
        proof,
        initial,
        endpoint,
        consumed,
        remaining,
    })
}

/// Five independently checked, closed, quantified prefix claims about the SAME
/// original full context. The first four cover budgets0..3. The final claim
/// covers every budget `extra+4`, with remaining `extra` and RUNNING pc4.
/// Each quantifies arbitrary `W`, admitted byte memory/host and two payloads
/// below2^32, including aliases. There is no provider-equality premise.
/// This is a theorem of the named CIC profile, not Rust/heap/native refinement,
/// default ByteV1 success, scalar/root substitution, ARC or body permission.
pub struct CheckedTaggedPrefixLaw<'receipt, 'source> {
    source: &'receipt CheckedSourceValueOperational<'source>,
    environment: Environment,
    prefixes: Vec<(Expr, Expr)>,
    handoff: (Expr, Expr),
}
impl<'source> CheckedTaggedPrefixLaw<'_, 'source> {
    pub fn source(&self) -> &CheckedSourceValueOperational<'source> {
        self.source
    }
    pub fn environment(&self) -> &Environment {
        &self.environment
    }
    pub fn prefix_claim(&self, budget: usize) -> Option<&Expr> {
        self.prefixes.get(budget).map(|p| &p.0)
    }
    pub fn prefix_proof(&self, budget: usize) -> Option<&Expr> {
        self.prefixes.get(budget).map(|p| &p.1)
    }
    pub fn handoff_claim(&self) -> &Expr {
        &self.handoff.0
    }
    pub fn handoff_proof(&self) -> &Expr {
        &self.handoff.1
    }
}

/// Derive and strictly replay the initialized universal prefix composition.
/// Actual canonical import checks and the constructive fixed-provider law are
/// composed before the profile's guarded Release/occurrence transitions. All
/// claims retain memory, host, activation owner/next and the exact budget.
/// A single construction ledger is shared across these five claims; ordinary
/// lookup/replay limits remain resource caps, not semantic assumptions.
pub fn check_tagged_u32_boxed_prefix_law<'receipt, 'source>(
    source: &'receipt CheckedSourceValueOperational<'source>,
    wrapper: FuncId,
    runtime_sources: &RuntimeSources<'_>,
    limits: crate::core_execution::Limits,
) -> Result<CheckedTaggedPrefixLaw<'receipt, 'source>, PrefixCicError> {
    runtime_sources
        .bind()
        .map_err(|e| PrefixCicError::Subject(format!("{e:?}")))?;
    let environment = checked_environment(source)?;
    let candidates =
        universal::derive(source, wrapper, &environment, limits).map_err(PrefixCicError::Replay)?;
    for (index, (claim, proof)) in candidates
        .prefixes
        .iter()
        .chain(std::iter::once(&candidates.handoff))
        .enumerate()
    {
        if let Err(error) = strict_replay(&environment, claim, proof) {
            // Preserve the original refusal. A separate diagnostic check can
            // explain a bad candidate, but never retry a resource stop or mint
            // a receipt from its result.
            let detail = if error.contains("resource stop")
                || clean_kernel::tc::declaration_budget_exhausted()
            {
                "resource stop; no additional checking".to_owned()
            } else {
                let mut checker = clean_kernel::TypeChecker::new(&environment);
                checker.set_allow_unsafe(false);
                checker.set_allow_partial(false);
                format!("{:?}", checker.check_type(proof, claim))
            };
            return Err(PrefixCicError::Replay(format!(
                "universal claim {index}: {error}; diagnostic {detail}"
            )));
        }
    }
    Ok(CheckedTaggedPrefixLaw {
        source,
        environment,
        prefixes: candidates.prefixes,
        handoff: candidates.handoff,
    })
}
