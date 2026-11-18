// Copyright 2026 Andrew Yates | Apache-2.0
//! Original nominal closure storage and a specific borrowed readback call.
//!
//! This is a source-analysis query, not an evaluator, execution receipt or
//! permission. It retains the real typed constructor, allocation, Store, Call
//! and callee Load/Return. Successful canonical source actions, capture codecs,
//! allocation/provenance, physical argument images and machine/frame refinement
//! remain separate obligations. In particular zero capture bytes prove nothing
//! about a target or initialization. The target below comes from the actual
//! stored constructor AND the same module's canonical storage binding.

use std::collections::BTreeSet;

use crate::closure_storage::ClosureStorageBinding;
use crate::{Block, BlockId, ClosureTyId, FuncId, Function, Inst, InstrNode, Module, Ty, ValueId};

const MAX_ROWS: usize = 4096;

/// One actual source coordinate, borrowed from the original immutable module.
#[derive(Clone, Copy, Debug)]
pub struct ClosureReadbackSite<'m> {
    function: FuncId,
    block: BlockId,
    instruction: usize,
    node: &'m InstrNode,
}
impl<'m> ClosureReadbackSite<'m> {
    pub fn function(&self) -> FuncId {
        self.function
    }
    pub fn block(&self) -> BlockId {
        self.block
    }
    pub fn instruction(&self) -> usize {
        self.instruction
    }
    pub fn node(&self) -> &'m InstrNode {
        self.node
    }
}

/// Conditional source readback data, with no publicly supplied target/value.
/// Captures remain the real source operands, not a replacement scalar shape.
/// The actual returned capture payload must still come from the callee result;
/// this query never substitutes the constructor's values for native loads.
pub struct BorrowedClosureReadback<'m> {
    module: &'m Module,
    nominal: ClosureTyId,
    binding: ClosureStorageBinding<'m>,
    slot: ValueId,
    stored_value: ValueId,
    capture_values: &'m [ValueId],
    constructor: ClosureReadbackSite<'m>,
    allocation: ClosureReadbackSite<'m>,
    store: ClosureReadbackSite<'m>,
    call: ClosureReadbackSite<'m>,
    load: ClosureReadbackSite<'m>,
    returned: ClosureReadbackSite<'m>,
}
impl std::fmt::Debug for BorrowedClosureReadback<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BorrowedClosureReadback")
            .field("caller", &self.call.function)
            .field("call_block", &self.call.block)
            .field("call_instruction", &self.call.instruction)
            .field("nominal", &self.nominal)
            .field("target", &self.binding.target)
            .field("slot", &self.slot)
            .finish_non_exhaustive()
    }
}

impl<'m> BorrowedClosureReadback<'m> {
    pub fn module(&self) -> &'m Module {
        self.module
    }
    pub fn nominal(&self) -> ClosureTyId {
        self.nominal
    }
    pub fn binding(&self) -> &ClosureStorageBinding<'m> {
        &self.binding
    }
    pub fn slot(&self) -> ValueId {
        self.slot
    }
    pub fn stored_value(&self) -> ValueId {
        self.stored_value
    }
    pub fn capture_values(&self) -> &'m [ValueId] {
        self.capture_values
    }
    pub fn constructor(&self) -> ClosureReadbackSite<'m> {
        self.constructor
    }
    pub fn allocation(&self) -> ClosureReadbackSite<'m> {
        self.allocation
    }
    pub fn store(&self) -> ClosureReadbackSite<'m> {
        self.store
    }
    pub fn call(&self) -> ClosureReadbackSite<'m> {
        self.call
    }
    pub fn load(&self) -> ClosureReadbackSite<'m> {
        self.load
    }
    pub fn returned(&self) -> ClosureReadbackSite<'m> {
        self.returned
    }
}

fn unique_function(module: &Module, id: FuncId) -> Result<&Function, &'static str> {
    let mut found = module.functions.iter().filter(|f| f.id == id);
    let function = found.next().ok_or("missing readback function")?;
    if found.next().is_some() || function.is_declaration() {
        return Err("ambiguous or bodyless readback function");
    }
    Ok(function)
}

fn source_ids(function: &Function) -> Result<(), &'static str> {
    let mut blocks = BTreeSet::new();
    let mut values = BTreeSet::new();
    let mut rows = 0usize;
    for block in &function.blocks {
        rows = rows
            .checked_add(1)
            .and_then(|n| n.checked_add(block.params.len()))
            .and_then(|n| n.checked_add(block.body.len()))
            .filter(|n| *n <= MAX_ROWS)
            .ok_or("borrowed closure source exceeds bounded profile")?;
        for node in &block.body {
            rows = rows
                .checked_add(node.results.len())
                .filter(|n| *n <= MAX_ROWS)
                .ok_or("borrowed closure result census exceeds bounded profile")?;
        }
        if !blocks.insert(block.id) {
            return Err("duplicate readback block identity");
        }
        for id in block
            .params
            .iter()
            .map(|(id, _)| id)
            .chain(block.body.iter().flat_map(|node| &node.results))
        {
            if !values.insert(*id) {
                return Err("duplicate readback SSA identity");
            }
        }
    }
    Ok(())
}

fn site<'m>(function: FuncId, block: &'m Block, instruction: usize) -> ClosureReadbackSite<'m> {
    ClosureReadbackSite {
        function,
        block: block.id,
        instruction,
        node: &block.body[instruction],
    }
}
fn aligned(actual: Option<u64>, natural: u64) -> bool {
    natural.is_power_of_two() && actual.is_none_or(|a| a == natural)
}
fn result(function: &Function, value: ValueId) -> Option<(&Block, usize)> {
    function.blocks.iter().find_map(|b| {
        b.body
            .iter()
            .position(|n| n.results.contains(&value))
            .map(|i| (b, i))
    })
}

impl Module {
    /// Query the exact source path for a direct Call's nominal Closure result.
    /// The bounded profile has a real typed Alloca and an immediately preceding
    /// typed Store of an actual same-block MakeClosure. The callee has exactly
    /// one plain Load through its sole pointer parameter, then returns that
    /// nominal value. All other uses of the fresh slot are checked over the
    /// COMPLETE caller, including unreachable blocks. A missing Store, imported
    /// value/target, escaped/aliased slot or writing callee remains a refusal.
    ///
    /// This does not claim that allocation/Store/Load succeeded. Under those
    /// canonical source conditions it identifies the returned target, not its
    /// physical representation or the equality/validity of captured pointers.
    pub fn borrowed_closure_readback(
        &self,
        caller: FuncId,
        returned_value: ValueId,
    ) -> Result<BorrowedClosureReadback<'_>, &'static str> {
        let function = unique_function(self, caller)?;
        source_ids(function)?;
        let (home, call_index) =
            result(function, returned_value).ok_or("missing readback Call result")?;
        let call = &home.body[call_index];
        let Inst::Call { callee, args } = &call.inst else {
            return Err("readback value is not a direct Call");
        };
        if call.results.as_slice() != [returned_value] || args.len() != 1 {
            return Err("readback Call requires one pointer and one nominal result");
        }
        let callee_function = unique_function(self, *callee)?;
        source_ids(callee_function)?;
        let signature = self
            .func_type(callee_function.ty)
            .ok_or("missing readback callee signature")?;
        let [Ty::Closure(nominal)] = signature.returns.as_slice() else {
            return Err("readback callee does not return one nominal Closure");
        };
        if signature.params != [Ty::Ptr] || signature.is_vararg || signature.abi.is_some() {
            return Err("readback callee signature is not the exact unadapted pointer boundary");
        }
        let declaration = self
            .closure_type(*nominal)
            .ok_or("missing readback closure declaration")?;
        let apparent = self
            .func_type(declaration.func)
            .ok_or("missing readback closure signature")?;
        if declaration.captures.len() > MAX_ROWS
            || apparent.params.len() > MAX_ROWS
            || apparent.returns.len() > MAX_ROWS
        {
            return Err("borrowed closure signature exceeds bounded profile");
        }
        let binding = self.closure_storage_binding(*nominal)?;
        let natural = binding.layout.align;
        let slot = args[0];
        let (allocation_block, allocation_index) =
            result(function, slot).ok_or("readback pointer has no Alloca")?;
        if allocation_block.id != home.id || allocation_index >= call_index {
            return Err("readback Alloca is not earlier in this exact block");
        }
        let allocation = &home.body[allocation_index];
        if allocation.results.as_slice() != [slot]
            || !matches!(&allocation.inst,
            Inst::Alloca { ty: Ty::Closure(id), count: None, align }
                if id == nominal && aligned(*align, natural))
        {
            return Err("readback Alloca changes nominal type, count or natural alignment");
        }
        let store_index = call_index
            .checked_sub(1)
            .ok_or("readback Call has no preceding Store")?;
        let store = &home.body[store_index];
        let stored_value = match &store.inst {
            Inst::Store {
                ty: Ty::Closure(id),
                ptr,
                value,
                volatile: false,
                align,
            } if id == nominal
                && *ptr == slot
                && aligned(*align, natural)
                && store.results.is_empty() =>
            {
                *value
            }
            _ => return Err("readback Call is not immediately preceded by its exact typed Store"),
        };
        if allocation_index >= store_index {
            return Err("readback Store precedes its Alloca");
        }
        let (constructor_block, constructor_index) =
            result(function, stored_value).ok_or("readback Store has no original constructor")?;
        if constructor_block.id != home.id || constructor_index >= store_index {
            return Err("readback constructor is not earlier in this exact block");
        }
        let constructor = &home.body[constructor_index];
        let captures = match &constructor.inst {
            Inst::MakeClosure { ty, func, captures }
                if ty == nominal
                    && *func == binding.target
                    && constructor.results.as_slice() == [stored_value]
                    && captures.len() == binding.captures.len() =>
            {
                captures
            }
            _ => return Err("readback Store is not the actual typed storage-bound constructor"),
        };
        for (capture, expected) in captures.iter().zip(binding.captures) {
            let declared = function
                .typed_value(self, *capture)
                .ok_or("readback capture has no declared SSA type")?;
            if &declared.ty != expected {
                return Err("readback capture SSA type differs from its declaration");
            }
            let before = home.params.iter().any(|(id, _)| id == capture)
                || home.body[..constructor_index]
                    .iter()
                    .any(|n| n.results.contains(capture));
            if !before {
                return Err("readback capture is not available before its constructor");
            }
        }
        // No pointer copy, GEP, import, other call or cross-block use can hide
        // behind a nominally equal slot. Actual addresses and memory authority
        // are still separate; this is only the original source use graph.
        for block in &function.blocks {
            for (index, node) in block.body.iter().enumerate() {
                if !node.inst.uses_value(slot) {
                    continue;
                }
                if block.id != home.id {
                    return Err("readback cell address escapes its block");
                }
                let allowed = match &node.inst {
                    Inst::Load {
                        ty: Ty::Closure(id),
                        ptr,
                        volatile: false,
                        align,
                    } => id == nominal && *ptr == slot && aligned(*align, natural),
                    Inst::Store {
                        ty: Ty::Closure(id),
                        ptr,
                        value,
                        volatile: false,
                        align,
                    } => {
                        id == nominal && *ptr == slot && *value != slot && aligned(*align, natural)
                    }
                    Inst::Call { .. } => index == call_index,
                    _ => false,
                };
                if !allowed {
                    return Err("readback cell address escapes or has a non-plain access");
                }
            }
        }
        if callee_function.blocks.len() != 1 {
            return Err("readback callee has additional source blocks");
        }
        let body = &callee_function.blocks[0];
        if body.id != callee_function.entry
            || body.params.len() != 1
            || body.params[0].1 != Ty::Ptr
            || body.body.len() != 2
        {
            return Err("readback callee is not the exact one-Load body");
        }
        let pointer = body.params[0].0;
        let load = &body.body[0];
        let [loaded] = load.results.as_slice() else {
            return Err("readback Load must bind one nominal value");
        };
        if !matches!(&load.inst, Inst::Load { ty: Ty::Closure(id), ptr, volatile: false, align }
            if id == nominal && *ptr == pointer && aligned(*align, natural))
        {
            return Err("readback callee changes the original Load type, pointer or alignment");
        }
        if !body.body[1].results.is_empty()
            || !matches!(&body.body[1].inst,
            Inst::Return { values } if values.as_slice() == [*loaded])
        {
            return Err("readback callee does not return its actual nominal Load result");
        }
        Ok(BorrowedClosureReadback {
            module: self,
            nominal: *nominal,
            binding,
            slot,
            stored_value,
            capture_values: captures,
            constructor: site(caller, home, constructor_index),
            allocation: site(caller, home, allocation_index),
            store: site(caller, home, store_index),
            call: site(caller, home, call_index),
            load: site(*callee, body, 0),
            returned: site(*callee, body, 1),
        })
    }
}

#[cfg(test)]
#[path = "borrowed_closure_readback_tests.rs"]
mod tests;
