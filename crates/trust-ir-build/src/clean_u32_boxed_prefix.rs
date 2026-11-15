// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! A source-bound observation of the actual boxed wrapper's first four nodes.
//!
//! This explicit LE64 tagged-UInt32 profile uses the landed runtime leaf model.
//! It is not ByteV1 or generic Interpreter execution, a CIC composition proof,
//! arithmetic output, native refinement, or body/codegen authority. Its node
//! budget belongs ONLY to this prefix machine. Admission precedes that budget.

use trust_ir::clean_boxed_u32::{Fault as RuntimeFault, FrameId, ReleaseEffect, UInt32Heap};
use trust_ir::{BlockId, CallingConv, Endianness, FuncId, Function, Inst, Module, Ty, ValueId};

use crate::core_reflection::CoreSignatureDescriptorProfileV1;
use crate::source_value_operational::CheckedSourceValueOperational;

/// A new target-model identity; no older evaluator receipt selects it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrefixProfile {
    CleanUInt32Tagged64PrefixV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrefixError {
    RetainedSubject,
    Target,
    ScalarDescriptor,
    WrapperDescriptor,
    WrapperGraph,
    UnboxDescriptor,
    BoxDescriptor,
    OutsideTaggedDomain { input: usize },
    Runtime(RuntimeFault),
    AtScalarHandoff,
}
impl core::fmt::Display for PrefixError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Clean UInt32 tagged-prefix refusal: {self:?}")
    }
}
impl std::error::Error for PrefixError {}
impl From<RuntimeFault> for PrefixError {
    fn from(value: RuntimeFault) -> Self {
        Self::Runtime(value)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrefixSite {
    pub function: FuncId,
    pub block: BlockId,
    pub node: usize,
}

/// An immutable binding to the SAME retained original module/source receipt.
/// Neither a supplied digest nor a newly assembled/sanitized module is accepted.
pub struct PreparedTaggedPrefix<'receipt, 'source> {
    scalar: &'receipt CheckedSourceValueOperational<'source>,
    wrapper: &'receipt Function,
    block: BlockId,
    params: [ValueId; 2],
    decoded: [ValueId; 2],
    unbox: FuncId,
    box_: FuncId,
}

fn unique_function(module: &Module, id: FuncId) -> Option<&Function> {
    let mut matches = module.functions.iter().filter(|f| f.id == id);
    let found = matches.next()?;
    matches.next().is_none().then_some(found)
}
fn signature_is(module: &Module, f: &Function, params: &[Ty], returns: &[Ty]) -> bool {
    f.calling_conv == CallingConv::C
        && module
            .func_types
            .get(f.ty.as_usize())
            .is_some_and(|sig| !sig.is_vararg && sig.params == params && sig.returns == returns)
}
fn single_result(node: &trust_ir::InstrNode) -> Option<ValueId> {
    match node.results.as_slice() {
        [result] => Some(*result),
        _ => None,
    }
}
fn call(node: &trust_ir::InstrNode) -> Option<(FuncId, &[ValueId])> {
    match &node.inst {
        Inst::Call { callee, args } => Some((*callee, args)),
        _ => None,
    }
}

/// Validate the complete seven-node wrapper BEFORE transferring any ownership.
/// Source/runtime identity and checked mathematics remain separate authorities.
pub fn prepare_tagged_u32_boxed_prefix<'receipt, 'source>(
    scalar: &'receipt CheckedSourceValueOperational<'source>,
    wrapper_id: FuncId,
) -> Result<PreparedTaggedPrefix<'receipt, 'source>, PrefixError> {
    let source = scalar.source_value();
    let module = source.module();
    let report = scalar
        .retained_validation_report()
        .ok_or(PrefixError::RetainedSubject)?;
    if !report
        .validated_module()
        .is_some_and(|original| core::ptr::eq(original, module))
        || scalar.signature_descriptor_profile()
            != CoreSignatureDescriptorProfileV1::RuntimeDeclarationsV1
    {
        return Err(PrefixError::RetainedSubject);
    }
    if !module
        .target_info
        .as_ref()
        .is_some_and(|target| target.pointer_size == 8 && target.endianness == Endianness::Little)
    {
        return Err(PrefixError::Target);
    }
    let plain = source.function();
    if !unique_function(module, plain.id).is_some_and(|f| core::ptr::eq(f, plain))
        || !signature_is(module, plain, &[Ty::U32, Ty::U32], &[Ty::U32])
    {
        return Err(PrefixError::ScalarDescriptor);
    }
    let wrapper = unique_function(module, wrapper_id).ok_or(PrefixError::WrapperDescriptor)?;
    if wrapper.id == plain.id || !signature_is(module, wrapper, &[Ty::Ptr, Ty::Ptr], &[Ty::Ptr]) {
        return Err(PrefixError::WrapperDescriptor);
    }
    let [block] = wrapper.blocks.as_slice() else {
        return Err(PrefixError::WrapperGraph);
    };
    let [(a, Ty::Ptr), (b, Ty::Ptr)] = block.params.as_slice() else {
        return Err(PrefixError::WrapperGraph);
    };
    if wrapper.entry != block.id || a == b {
        return Err(PrefixError::WrapperGraph);
    }
    let [n0, n1, n2, n3, n4, n5, n6] = block.body.as_slice() else {
        return Err(PrefixError::WrapperGraph);
    };
    let (unbox, args0) = call(n0).ok_or(PrefixError::WrapperGraph)?;
    let (unbox1, args1) = call(n1).ok_or(PrefixError::WrapperGraph)?;
    let ua = single_result(n0).ok_or(PrefixError::WrapperGraph)?;
    let ub = single_result(n1).ok_or(PrefixError::WrapperGraph)?;
    let (selected, args4) = call(n4).ok_or(PrefixError::WrapperGraph)?;
    let value = single_result(n4).ok_or(PrefixError::WrapperGraph)?;
    let (box_, args5) = call(n5).ok_or(PrefixError::WrapperGraph)?;
    let output = single_result(n5).ok_or(PrefixError::WrapperGraph)?;
    let release = |node: &trust_ir::InstrNode, expected| {
        matches!(node.inst, Inst::Release { ptr } if ptr == expected) && node.results.is_empty()
    };
    if args0 != [*a]
        || args1 != [*b]
        || unbox != unbox1
        || !release(n2, *a)
        || !release(n3, *b)
        || selected != plain.id
        || args4 != [ua, ub]
        || args5 != [value]
        || !matches!(&n6.inst, Inst::Return { values } if values == &[output])
        || !n6.results.is_empty()
    {
        return Err(PrefixError::WrapperGraph);
    }
    let ids = [*a, *b, ua, ub, value, output];
    if ids.iter().collect::<std::collections::BTreeSet<_>>().len() != ids.len() {
        return Err(PrefixError::WrapperGraph);
    }
    let unbox_decl = unique_function(module, unbox).ok_or(PrefixError::UnboxDescriptor)?;
    if !unbox_decl.is_declaration()
        || unbox_decl.name != "clean_unbox_uint32"
        || !signature_is(module, unbox_decl, &[Ty::Ptr], &[Ty::U32])
    {
        return Err(PrefixError::UnboxDescriptor);
    }
    let box_decl = unique_function(module, box_).ok_or(PrefixError::BoxDescriptor)?;
    if !box_decl.is_declaration()
        || box_decl.name != "clean_box_uint32"
        || !signature_is(module, box_decl, &[Ty::U32], &[Ty::Ptr])
    {
        return Err(PrefixError::BoxDescriptor);
    }
    Ok(PreparedTaggedPrefix {
        scalar,
        wrapper,
        block: block.id,
        params: [*a, *b],
        decoded: [ua, ub],
        unbox,
        box_,
    })
}

impl<'receipt, 'source> PreparedTaggedPrefix<'receipt, 'source> {
    pub fn profile(&self) -> PrefixProfile {
        PrefixProfile::CleanUInt32Tagged64PrefixV1
    }
    pub fn scalar(&self) -> &'receipt CheckedSourceValueOperational<'source> {
        self.scalar
    }
    pub fn wrapper(&self) -> &'receipt Function {
        self.wrapper
    }
    pub fn unbox_id(&self) -> FuncId {
        self.unbox
    }
    pub fn box_id(&self) -> FuncId {
        self.box_
    }
    /// Admission is outside the prefix node budget. Heap carriers, even valid
    /// UInt32 heap boxes, are outside THIS deliberately tagged-only profile.
    /// The heap is caller-owned; failures retain it in the returned refusal.
    pub fn start(
        self,
        mut heap: UInt32Heap,
        words: [u64; 2],
        node_budget: u64,
    ) -> Result<TaggedPrefixMachine<'receipt, 'source>, Box<PrefixAdmissionRefusal>> {
        for (input, word) in words.iter().enumerate() {
            if word & 1 == 0 {
                return Err(Box::new(PrefixAdmissionRefusal {
                    error: PrefixError::OutsideTaggedDomain { input },
                    heap,
                }));
            }
            if let Err(error) = heap.decode(*word) {
                return Err(Box::new(PrefixAdmissionRefusal {
                    error: error.into(),
                    heap,
                }));
            }
        }
        let frame = match heap.begin(&words) {
            Ok(frame) => frame,
            Err(error) => {
                return Err(Box::new(PrefixAdmissionRefusal {
                    error: error.into(),
                    heap,
                }));
            }
        };
        Ok(TaggedPrefixMachine {
            binding: self,
            heap,
            frame,
            node: 0,
            remaining_budget: node_budget,
            decoded: [None, None],
        })
    }
}

#[derive(Debug)]
pub struct PrefixAdmissionRefusal {
    pub error: PrefixError,
    pub heap: UInt32Heap,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrefixStep {
    NoBudget {
        next: PrefixSite,
    },
    Decoded {
        site: PrefixSite,
        callee: FuncId,
        input: ValueId,
        result: ValueId,
        value: u32,
    },
    Released {
        site: PrefixSite,
        operand: ValueId,
        slot: usize,
        effect: ReleaseEffect,
    },
}

/// Observable MODEL state, not a certificate or Byte world projection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrefixSnapshot {
    pub profile: PrefixProfile,
    pub next: PrefixSite,
    pub executed_nodes: usize,
    pub remaining_budget: u64,
    pub decoded: [Option<(ValueId, u32)>; 2],
    pub remaining_owned_slots: [bool; 2],
    /// Local to this snapshot's model heap, never a cross-world capability.
    pub model_frame: FrameId,
    pub heap: UInt32Heap,
}

pub struct TaggedPrefixMachine<'receipt, 'source> {
    binding: PreparedTaggedPrefix<'receipt, 'source>,
    heap: UInt32Heap,
    frame: FrameId,
    node: usize,
    remaining_budget: u64,
    decoded: [Option<(ValueId, u32)>; 2],
}

/// A typed handoff to the ACTUAL scalar call, with no fabricated scalar result.
pub struct ScalarCallHandoff<'a, 'source> {
    pub profile: PrefixProfile,
    pub source: &'a CheckedSourceValueOperational<'source>,
    pub site: PrefixSite,
    pub actual_call: &'a trust_ir::InstrNode,
    pub callee: FuncId,
    pub operands: [(ValueId, u32); 2],
    pub remaining_owned_slots: [bool; 2],
    pub remaining_budget: u64,
}

impl<'receipt, 'source> TaggedPrefixMachine<'receipt, 'source> {
    fn site(&self) -> PrefixSite {
        PrefixSite {
            function: self.binding.wrapper.id,
            block: self.binding.block,
            node: self.node,
        }
    }
    fn remaining_slots(&self) -> Result<[bool; 2], PrefixError> {
        let live = |slot| -> Result<bool, PrefixError> {
            match self.heap.decode_input(self.frame, slot) {
                Ok(_) => Ok(true),
                Err(RuntimeFault::ReleasedInput) => Ok(false),
                Err(error) => Err(error.into()),
            }
        };
        Ok([live(0)?, live(1)?])
    }
    pub fn snapshot(&self) -> Result<PrefixSnapshot, PrefixError> {
        Ok(PrefixSnapshot {
            profile: self.binding.profile(),
            next: self.site(),
            executed_nodes: self.node,
            remaining_budget: self.remaining_budget,
            decoded: self.decoded,
            remaining_owned_slots: self.remaining_slots()?,
            model_frame: self.frame,
            heap: self.heap.clone(),
        })
    }
    /// Execute ONE actual prefix node. Exhaustion changes no state. This budget
    /// makes no ByteV1/reference-interpreter fuel-equivalence assertion.
    pub fn step(&mut self) -> Result<PrefixStep, PrefixError> {
        if self.node == 4 {
            return Err(PrefixError::AtScalarHandoff);
        }
        let site = self.site();
        if self.remaining_budget == 0 {
            return Ok(PrefixStep::NoBudget { next: site });
        }
        // Fetch from the same immutable original body, never a substitute module.
        let actual = self
            .binding
            .wrapper
            .blocks
            .first()
            .and_then(|block| block.body.get(self.node))
            .ok_or(PrefixError::WrapperGraph)?;
        let slot = match self.node {
            0 | 2 => 0,
            1 | 3 => 1,
            _ => return Err(PrefixError::WrapperGraph),
        };
        let event = if self.node < 2 {
            let (callee, args) = call(actual).ok_or(PrefixError::WrapperGraph)?;
            if callee != self.binding.unbox || args != [self.binding.params[slot]] {
                return Err(PrefixError::WrapperGraph);
            }
            let value = self.heap.decode_input(self.frame, slot)?;
            let input = self.binding.params[slot];
            let result = single_result(actual).ok_or(PrefixError::WrapperGraph)?;
            if result != self.binding.decoded[slot] {
                return Err(PrefixError::WrapperGraph);
            }
            self.decoded[slot] = Some((result, value));
            PrefixStep::Decoded {
                site,
                callee: self.binding.unbox,
                input,
                result,
                value,
            }
        } else {
            if !matches!(actual.inst, Inst::Release { ptr } if ptr == self.binding.params[slot])
                || !actual.results.is_empty()
            {
                return Err(PrefixError::WrapperGraph);
            }
            let effect = self.heap.release(self.frame, slot)?;
            PrefixStep::Released {
                site,
                operand: self.binding.params[slot],
                slot,
                effect,
            }
        };
        self.remaining_budget -= 1;
        self.node += 1;
        Ok(event)
    }
    pub fn handoff(&self) -> Result<Option<ScalarCallHandoff<'_, 'source>>, PrefixError> {
        if self.node != 4 {
            return Ok(None);
        }
        let [Some(a), Some(b)] = self.decoded else {
            return Err(PrefixError::WrapperGraph);
        };
        let actual_call = self
            .binding
            .wrapper
            .blocks
            .first()
            .and_then(|block| block.body.get(4))
            .ok_or(PrefixError::WrapperGraph)?;
        Ok(Some(ScalarCallHandoff {
            profile: self.binding.profile(),
            source: self.binding.scalar,
            site: self.site(),
            actual_call,
            callee: self.binding.scalar.source_value().function().id,
            operands: [a, b],
            remaining_owned_slots: self.remaining_slots()?,
            remaining_budget: self.remaining_budget,
        }))
    }
}
