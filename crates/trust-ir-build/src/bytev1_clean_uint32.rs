// Copyright 2026 Andrew Yates | Apache-2.0
//! Concrete Clean UInt32 providers for the existing canonical ByteV1 call rule.
//! No independent instruction evaluator and no caller-selected host callback.
//! Source binding is not native linkage, a body license or Trust Certified credit.
use clean_kernel::{Expr, Name, TypeChecker};
use clean_verify::{
    eval_ir::{EvalIrVocabulary, shared_specification_with_stack},
    spec::Specification,
};
use trust_ir::{
    CallingConv, Endianness, FuncId, Inst, Module, Ty, clean_boxed_u32::RuntimeSourceBinding,
};

pub struct CheckedRuntimeProfile {
    decode: FuncId,
    encode: FuncId,
    release: FuncId,
    module_digest: trust_ir::proof::ProofDigest,
}
impl CheckedRuntimeProfile {
    pub fn new(module: &Module, _: RuntimeSourceBinding) -> Result<Self, String> {
        let target = module
            .target_info
            .as_ref()
            .ok_or("runtime profile needs an explicit target")?;
        if target.pointer_size != 8 || target.endianness != Endianness::Little {
            return Err("Clean UInt32 runtime requires pointer64 little endian".into());
        }
        let ids: std::collections::BTreeSet<_> = module.functions.iter().map(|f| f.id).collect();
        if ids.len() != module.functions.len() {
            return Err("duplicate function IDs in runtime profile".into());
        }
        let find = |name: &str, params: &[Ty], returns: &[Ty]| -> Result<FuncId, String> {
            let mut found = module.functions.iter().filter(|f| f.name == name);
            let f = found.next().ok_or_else(|| format!("missing {name}"))?;
            if found.next().is_some() || !f.is_declaration() || f.calling_conv != CallingConv::C {
                return Err(format!("ambiguous or defined/non-C runtime {name}"));
            }
            let sig = module
                .func_types
                .get(f.ty.as_usize())
                .ok_or("runtime signature missing")?;
            if sig.params != params || sig.returns != returns || sig.is_vararg || sig.abi.is_some()
            {
                return Err(format!("runtime signature mismatch: {name}"));
            }
            Ok(f.id)
        };
        Ok(Self {
            decode: find("clean_unbox_uint32", &[Ty::Ptr], &[Ty::U32])?,
            encode: find("clean_box_uint32", &[Ty::U32], &[Ty::Ptr])?,
            release: find("clean_dec", &[Ty::Ptr], &[])?,
            module_digest: module.stable_digest(),
        })
    }
    pub fn module_digest(&self) -> &trust_ir::proof::ProofDigest {
        &self.module_digest
    }
    /// An explicit, separately scoped normalization witness. Never mutates the
    /// original module or changes the default whole-module reflector's refusal.
    /// Its simulation obligation is NOT a body/codegen certificate.
    pub fn release_call(&self, module: &Module, instruction: &Inst) -> Result<Inst, String> {
        if module.stable_digest() != self.module_digest {
            return Err("runtime profile belongs to different complete module".into());
        }
        match instruction {
            Inst::Release { ptr } => Ok(Inst::Call {
                callee: self.release,
                args: vec![*ptr],
            }),
            _ => Err("runtime normalization requires an actual Release".into()),
        }
    }
    pub fn providers(&self) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("ir_cu32_provider_v1"), vec![]),
            [self.decode, self.encode, self.release].map(|id| Expr::nat_lit(u64::from(id.index()))),
        )
    }
}
/// Sealed canonical semantics owner. Callers cannot substitute a look-alike
/// environment for refinement replay or shadow a runtime definition.
pub struct RuntimeSpecification(Specification, std::collections::BTreeMap<String, [u8; 32]>);
impl RuntimeSpecification {
    pub fn fingerprints(&self) -> &std::collections::BTreeMap<String, [u8; 32]> {
        &self.1
    }
    pub fn env(&self) -> &clean_kernel::Environment {
        self.0.env()
    }
    pub fn get_definition(&self, name: &str) -> Option<&clean_verify::spec::SpecDefinition> {
        self.0.get_definition(name)
    }
}
/// Extend a fresh owned copy of the actual canonical ByteV1 package, then
/// independently kernel-check and audit every new root. No kernel tree changes.
pub fn specification() -> Result<RuntimeSpecification, String> {
    let mut spec = shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .map_err(|e| e.to_string())?
        .clone();
    let before: std::collections::HashSet<_> = spec.definitions().keys().cloned().collect();
    for source in include_str!("bytev1_clean_uint32/definitions.lean").split("\n\n") {
        let source = source.trim();
        if source.is_empty() {
            continue;
        }
        if source.starts_with("inductive ") {
            spec.add_inductive(source, "Typed per-frame transferred-credit runtime state")
                .map_err(|e| e.to_string())?;
        } else {
            spec.add_recursive_def(
                source,
                "Concrete UInt32 handler in canonical ByteV1 memory/provider semantics",
            )
            .map_err(|e| e.to_string())?;
        }
    }
    let env = spec.env();
    for (name, def) in spec.definitions() {
        if before.contains(name) || def.elaborated_value.is_none() {
            continue;
        }
        let ty = def
            .elaborated_type
            .as_ref()
            .ok_or_else(|| format!("missing type {name}"))?;
        let value = def
            .elaborated_value
            .as_ref()
            .ok_or_else(|| format!("missing value {name}"))?;
        let mut tc = TypeChecker::new(env);
        tc.set_allow_unsafe(false);
        tc.set_allow_partial(false);
        tc.check_type(value, ty)
            .map_err(|e| format!("runtime root {name}: {e:?}"))?;
        let n = Name::from_string(name);
        if tc.heartbeat_spent()
            || env.axiom_deps(&n).is_none_or(|a| !a.is_empty())
            || env.trust_marker_deps(&n).is_none_or(|a| !a.is_empty())
        {
            return Err(format!(
                "runtime root not independently checked/audited: {name}"
            ));
        }
    }
    let roots = [
        "ir_cu32_provider_v1",
        "ir_cu32_owned_guard_v1",
        "ir_cu32_allocation_at_v1",
        "ir_cu32_credit_for_v1",
        "ir_cu32_decode_heap_law_v1",
        "ir_cu32_release_heap_law_v1",
        "ir_cu32_rc_write_frame_v1",
        "ir_cu32_other_frame_credit_v1",
        "ir_cu32_drop_preserves_owners_v1",
    ];
    let mut fingerprint = std::collections::BTreeMap::new();
    for root in roots {
        fingerprint.insert(
            root.to_owned(),
            spec.env()
                .closure_digest(&Name::from_string(root))
                .map_err(|e| format!("runtime semantic identity {root}: {e:?}"))?,
        );
    }
    Ok(RuntimeSpecification(spec, fingerprint))
}

fn constant(name: &str) -> Expr {
    Expr::const_(
        Name::from_string(name),
        if name == "Bool.rec" {
            vec![clean_kernel::Level::succ(clean_kernel::Level::zero())]
        } else {
            vec![]
        },
    )
}
fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(constant(name), args)
}
fn nat(n: u64) -> Expr {
    Expr::nat_lit(n)
}
fn list(ty: &str, values: impl IntoIterator<Item = Expr>) -> Expr {
    let values: Vec<_> = values.into_iter().collect();
    values
        .into_iter()
        .rev()
        .fold(app("IRList.nil", [constant(ty)]), |tail, head| {
            app("IRList.cons", [constant(ty), head, tail])
        })
}
/// Source-model heap-fragment embedding into the ACTUAL ByteV1 memory and host
/// types. All heap rows use persistent owner0; canonical stack rows/frames are
/// a separate disjoint frame. No fact about a native address/image is supplied.
pub struct ProjectedRuntimeState {
    pub memory: Expr,
    pub host: Expr,
    pub active_owner: u64,
}
/// Accounts for every live source frame with an injective positive ByteV1 owner
/// map. Its alignment metadata is the actual source allocation layout, not an
/// assumed pointer-divisibility promise. Generic unrelated bytes are retained.
pub fn project(
    heap: &trust_ir::clean_boxed_u32::UInt32Heap,
    active: trust_ir::clean_boxed_u32::FrameId,
    owners: &[(trust_ir::clean_boxed_u32::FrameId, u64)],
) -> Result<ProjectedRuntimeState, String> {
    use clean_kernel::BinderInfo;
    use std::collections::{BTreeMap, BTreeSet};
    let frames = heap.transferred_inputs();
    let owner_map: BTreeMap<_, _> = owners.iter().copied().collect();
    if owner_map.len() != owners.len()
        || owner_map.len() != frames.len()
        || owners.iter().any(|(_, o)| *o == 0)
        || owners.iter().map(|(_, o)| o).collect::<BTreeSet<_>>().len() != owners.len()
        || frames.iter().any(|(f, _)| !owner_map.contains_key(f))
    {
        return Err("runtime owner map must account injectively for every live frame".into());
    }
    let active_owner = *owner_map
        .get(&active)
        .ok_or("active runtime frame is not live")?;
    let mut bytes = app("IROption.none", [constant("Nat")]);
    let mut alignment = nat(0);
    let mut rows = Vec::new();
    let mut next = 0;
    for image in heap.allocations().values().rev() {
        next = next.max(
            image
                .address
                .checked_add(image.bytes.len() as u64)
                .ok_or("snapshot address overflow")?,
        );
        rows.push(app(
            "IRByteAllocationV1.mk",
            [
                nat(image.address),
                nat(image.bytes.len() as u64),
                nat(0),
                constant(if image.live {
                    "Bool.true"
                } else {
                    "Bool.false"
                }),
            ],
        ));
        alignment = app(
            "Bool.rec",
            [
                Expr::lam(BinderInfo::Default, constant("Bool"), constant("Nat")),
                alignment,
                nat(image.alignment),
                app("ir_nat_eqb", [Expr::bvar(0), nat(image.address)]),
            ],
        );
        for (i, b) in image.bytes.iter().enumerate().rev() {
            let v = b.map_or_else(
                || app("IROption.none", [constant("Nat")]),
                |v| app("IROption.some", [constant("Nat"), nat(u64::from(v))]),
            );
            bytes = app(
                "Bool.rec",
                [
                    Expr::lam(
                        BinderInfo::Default,
                        constant("Bool"),
                        app("IROption", [constant("Nat")]),
                    ),
                    bytes,
                    v,
                    app("ir_nat_eqb", [Expr::bvar(0), nat(image.address + i as u64)]),
                ],
            );
        }
    }
    let memory = app(
        "IRByteMemoryV1.mk",
        [
            list("IRByteAllocationV1", rows),
            Expr::lam(BinderInfo::Default, constant("Nat"), bytes),
            nat(next),
        ],
    );
    let mut counts = BTreeMap::<(u64, u64), u64>::new();
    for (id, words) in frames {
        for word in words {
            *counts.entry((owner_map[&id], word)).or_default() += 1;
        }
    }
    let mut bank = nat(0);
    for ((owner, address), count) in counts {
        bank = app(
            "Bool.rec",
            [
                Expr::lam(BinderInfo::Default, constant("Bool"), constant("Nat")),
                bank,
                nat(count),
                app(
                    "Bool.and",
                    [
                        app("ir_nat_eqb", [Expr::bvar(1), nat(owner)]),
                        app("ir_nat_eqb", [Expr::bvar(0), nat(address)]),
                    ],
                ),
            ],
        );
    }
    let host = app(
        "IRCU32HostV1.mk",
        [
            nat(active_owner),
            Expr::lam(
                BinderInfo::Default,
                constant("Nat"),
                Expr::lam(BinderInfo::Default, constant("Nat"), bank),
            ),
            Expr::lam(BinderInfo::Default, constant("Nat"), alignment),
        ],
    );
    Ok(ProjectedRuntimeState {
        memory,
        host,
        active_owner,
    })
}

#[derive(Debug, Clone, Copy)]
pub enum RuntimeOperation {
    Decode { word: u64 },
    Encode { value: u32 },
    Release { slot: usize },
}
/// A pointwise, independently replayed mathematical runtime transition.
/// No body/source-to-machine license or global Rust refinement is conferred.
/// Claims expose the full provider input/result and source-poststate byte/credit
/// observations; generic write/other-frame laws cover the untouched frame.
pub struct CheckedRuntimeTransition {
    runtime_closures: std::collections::BTreeMap<String, [u8; 32]>,
    module_digest: trust_ir::proof::ProofDigest,
    statements: Vec<(Expr, Expr)>,
    after: trust_ir::clean_boxed_u32::UInt32Heap,
    result: Expr,
}
impl CheckedRuntimeTransition {
    pub fn source_after(&self) -> &trust_ir::clean_boxed_u32::UInt32Heap {
        &self.after
    }
    pub fn provider_result(&self) -> &Expr {
        &self.result
    }
    pub fn statements(&self) -> &[(Expr, Expr)] {
        &self.statements
    }
    pub fn module_digest(&self) -> &trust_ir::proof::ProofDigest {
        &self.module_digest
    }
    pub fn replay(&self, specification: &RuntimeSpecification) -> Result<(), String> {
        if &self.runtime_closures != specification.fingerprints() {
            return Err("runtime semantic closure changed; no same-name replay".into());
        }
        for (claim, term) in &self.statements {
            check(specification, claim, term)?;
        }
        Ok(())
    }
}
fn equality(ty: Expr, a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq"),
            vec![clean_kernel::Level::succ(clean_kernel::Level::zero())],
        ),
        [ty, a, b],
    )
}
fn reflexivity(ty: Expr, a: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![clean_kernel::Level::succ(clean_kernel::Level::zero())],
        ),
        [ty, a],
    )
}
fn check(spec: &RuntimeSpecification, claim: &Expr, term: &Expr) -> Result<(), String> {
    let mut tc = TypeChecker::new(spec.env());
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    tc.check_type(claim, &Expr::sort(clean_kernel::Level::zero()))
        .map_err(|e| format!("runtime claim: {e:?}"))?;
    tc.check_type(term, claim)
        .map_err(|e| format!("runtime refinement replay: {e:?}"))?;
    if tc.heartbeat_spent()
        || clean_kernel::tc::declaration_budget_exhausted()
        || !spec.env().audit_certification(claim, term).is_certified()
    {
        return Err("runtime replay not judged/certifiable".into());
    }
    Ok(())
}
fn import_result(outcome: Expr, memory: Expr, host: Expr) -> Expr {
    app(
        "IRByteImportResultV1.mk",
        [constant("IRCU32HostV1"), outcome, memory, host],
    )
}
impl CheckedRuntimeProfile {
    /// Recompute the source operation, derive the actual canonical-provider
    /// result, and replay its complete equality and poststate observations.
    /// The initial bytes, alignment and transferred credits are explicit model
    /// inputs, never a claim that native memory implements them.
    pub fn check_transition(
        &self,
        spec: &RuntimeSpecification,
        heap: &trust_ir::clean_boxed_u32::UInt32Heap,
        frame: trust_ir::clean_boxed_u32::FrameId,
        owners: &[(trust_ir::clean_boxed_u32::FrameId, u64)],
        op: RuntimeOperation,
    ) -> Result<CheckedRuntimeTransition, String> {
        use trust_ir::clean_boxed_u32::{ReleaseEffect, encode};
        let before = project(heap, frame, owners)?;
        let mut after = heap.clone();
        let mut memory = before.memory.clone();
        let mut host = before.host.clone();
        let (fid, arg, values) = match op {
            RuntimeOperation::Decode { word } => {
                let value = heap
                    .decode(word)
                    .map_err(|e| format!("source borrowing admission: {e:?}"))?;
                (
                    self.decode,
                    app("IRScalar.ptr_", [nat(word)]),
                    list("IRScalar", [app("IRScalar.int_", [nat(u64::from(value))])]),
                )
            }
            RuntimeOperation::Encode { value } => (
                self.encode,
                app("IRScalar.int_", [nat(u64::from(value))]),
                list(
                    "IRScalar",
                    [app("IRScalar.ptr_", [nat(encode(value).word())])],
                ),
            ),
            RuntimeOperation::Release { slot } => {
                let word = heap
                    .transferred_input(frame, slot)
                    .map_err(|e| format!("source ownership admission: {e:?}"))?;
                let effect = after
                    .release(frame, slot)
                    .map_err(|e| format!("source Release admission: {e:?}"))?;
                let written = match effect {
                    ReleaseEffect::Decremented { after, .. } => Some((false, u64::from(after))),
                    ReleaseEffect::Freed { .. } => Some((true, u64::from(u32::MAX))),
                    _ => None,
                };
                if let Some((freed, rc)) = written {
                    let allocs = app("ir_byte_mem_allocs_v1", [memory.clone()]);
                    memory = app(
                        "IRByteMemoryV1.mk",
                        [
                            if freed {
                                app("ir_cu32_retire_leaf_v1", [nat(word), allocs])
                            } else {
                                allocs
                            },
                            app(
                                "ir_byte_write_word_v1",
                                [
                                    app("ir_byte_mem_bytes_v1", [memory.clone()]),
                                    nat(word),
                                    nat(4),
                                    nat(rc),
                                ],
                            ),
                            app("ir_byte_mem_next_v1", [memory.clone()]),
                        ],
                    );
                }
                host = app("ir_cu32_spend_v1", [host, nat(word)]);
                (
                    self.release,
                    app("IRScalar.ptr_", [nat(word)]),
                    list("IRScalar", []),
                )
            }
        };
        let actual = Expr::apps(
            self.providers(),
            [
                nat(u64::from(fid.index())),
                list("IRScalar", [arg]),
                before.memory.clone(),
                before.host.clone(),
            ],
        );
        let result = import_result(app("IROutcome.ret", [values]), memory.clone(), host.clone());
        let ty = app("IRByteImportResultV1", [constant("IRCU32HostV1")]);
        let mut statements = vec![(
            equality(ty.clone(), actual, result.clone()),
            reflexivity(ty, result.clone()),
        )];
        // The native ordinary count is refs-minus-one. Do not trust the Rust
        // import/transfer code for this premise: replay both pre/post banks
        // against the actual header bytes in the canonical byte model.
        let owner_list = list("Nat", owners.iter().map(|(_, o)| nat(*o)));
        let owned_words: std::collections::BTreeSet<_> = heap
            .transferred_inputs()
            .into_iter()
            .flat_map(|(_, w)| w)
            .collect();
        for word in owned_words {
            for (mem, bank) in [
                (before.memory.clone(), before.host.clone()),
                (memory.clone(), host.clone()),
            ] {
                let guard = app(
                    "ir_cu32_owned_guard_v1",
                    [mem, bank, owner_list.clone(), nat(word)],
                );
                statements.push((
                    equality(constant("Bool"), guard, constant("Bool.true")),
                    reflexivity(constant("Bool"), constant("Bool.true")),
                ));
            }
        }
        // Finite source-image observations are checked, not equated by Rust.
        // The generic RC-write frame law separately quantifies every outside
        // address, including bytes not enumerated in this heap fragment.
        for image in after.allocations().values() {
            let expected_row = app(
                "IROption.some",
                [
                    constant("IRByteAllocationV1"),
                    app(
                        "IRByteAllocationV1.mk",
                        [
                            nat(image.address),
                            nat(image.bytes.len() as u64),
                            nat(0),
                            constant(if image.live {
                                "Bool.true"
                            } else {
                                "Bool.false"
                            }),
                        ],
                    ),
                ],
            );
            let actual_row = app(
                "ir_cu32_allocation_at_v1",
                [
                    app("ir_byte_mem_allocs_v1", [memory.clone()]),
                    nat(image.address),
                ],
            );
            let row_ty = app("IROption", [constant("IRByteAllocationV1")]);
            statements.push((
                equality(row_ty.clone(), actual_row, expected_row.clone()),
                reflexivity(row_ty, expected_row),
            ));

            for (i, expected) in image.bytes.iter().enumerate() {
                let expected = expected.map_or_else(
                    || app("IROption.none", [constant("Nat")]),
                    |n| app("IROption.some", [constant("Nat"), nat(u64::from(n))]),
                );
                let actual = Expr::app(
                    app("ir_byte_mem_bytes_v1", [memory.clone()]),
                    nat(image.address + i as u64),
                );
                let ty = app("IROption", [constant("Nat")]);
                statements.push((
                    equality(ty.clone(), actual, expected.clone()),
                    reflexivity(ty, expected),
                ));
            }
        }
        let post = project(&after, frame, owners)?;
        for &(_, owner) in owners {
            let words: std::collections::BTreeSet<_> = heap
                .transferred_inputs()
                .into_iter()
                .flat_map(|(_, w)| w)
                .collect();
            for word in words {
                let actual = app(
                    "ir_cu32_credit_for_v1",
                    [host.clone(), nat(owner), nat(word)],
                );
                let expected = app(
                    "ir_cu32_credit_for_v1",
                    [post.host.clone(), nat(owner), nat(word)],
                );
                let ty = constant("Nat");
                statements.push((
                    equality(ty.clone(), actual, expected.clone()),
                    reflexivity(ty, expected),
                ));
            }
        }
        let checked = CheckedRuntimeTransition {
            runtime_closures: spec.fingerprints().clone(),
            module_digest: self.module_digest,
            statements,
            after,
            result,
        };
        checked.replay(spec)?;
        Ok(checked)
    }
}

/// Complete execution-only module image with an explicit Release-call transport.
/// No table or declaration is pruned; no proof annotation or body grade is
/// promoted. Default metadata/ABI refusals remain in force at reflection.
pub struct RuntimeModule {
    module: Module,
    source_digest: trust_ir::proof::ProofDigest,
}
impl RuntimeModule {
    pub fn source_digest(&self) -> &trust_ir::proof::ProofDigest {
        &self.source_digest
    }
    pub fn module(&self) -> &Module {
        &self.module
    }
    pub fn reflect(
        &self,
        addresses: &[(FuncId, u64)],
    ) -> Result<
        crate::core_reflection::ReflectedCoreModuleV1<'_>,
        crate::core_reflection::CoreReflectionError,
    > {
        crate::core_reflection::reflect_core_module_v1(&self.module, addresses)
    }
}
impl CheckedRuntimeProfile {
    /// Preserve the COMPLETE module while exposing the runtime's explicit
    /// release-call normalization to the canonical, unchanged ByteV1 dispatcher.
    /// Instruction simulation is checked by the concrete runtime transition
    /// component; this is not a helper-body translation-validation certificate.
    pub fn execution_module(&self, source: &Module) -> Result<RuntimeModule, String> {
        if source.stable_digest() != self.module_digest {
            return Err("complete runtime source identity changed".into());
        }
        let mut module = source.clone();
        for f in &mut module.functions {
            for b in &mut f.blocks {
                for node in &mut b.body {
                    if let Inst::Release { ptr } = &node.inst {
                        let ptr = *ptr;
                        node.inst = Inst::Call {
                            callee: self.release,
                            args: vec![ptr],
                        };
                    }
                }
            }
        }
        Ok(RuntimeModule {
            module,
            source_digest: self.module_digest,
        })
    }
}
