// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! The actual acyclic entry prefix before one authenticated natural-loop header.
//! This is only a CFG analysis projection. The original remains borrowed and
//! unchanged; typed source/SSA, effect custody and a boundary meaning are still
//! mandatory. Never emit or execute the projection as an SSA endpoint.
use crate::loop_cut::NaturalLoopCut;
use std::collections::{BTreeSet, HashMap};
use trust_ir::{BlockId, Function, Inst, ValueId, analysis::DominatorTree};

pub struct EntryPrefixCut<'f> {
    loop_cut: NaturalLoopCut<'f>,
    analysis: Function,
    order: Vec<BlockId>,
}
impl<'f> EntryPrefixCut<'f> {
    pub fn new(original: &'f Function, header: BlockId) -> Result<Self, String> {
        let _instruction_count = original.blocks.iter().try_fold(0usize, |sum, block| {
            sum.checked_add(block.body.len())
                .filter(|n| *n <= 1_000_000)
                .ok_or("entry-prefix instruction budget")
        })?;
        let loop_cut = NaturalLoopCut::new(original, header)?;
        if loop_cut.external_values().len() > 65_536 {
            return Err("entry-prefix capture budget".into());
        }
        let dom = DominatorTree::new(original);
        let mut definitions = HashMap::new();
        for block in &original.blocks {
            for value in block.params.iter().map(|(id, _)| *id).chain(
                block
                    .body
                    .iter()
                    .flat_map(|node| node.results.iter().copied()),
            ) {
                if definitions.insert(value, block.id).is_some() {
                    return Err("entry-prefix source has duplicate SSA definition".into());
                }
            }
        }
        for value in loop_cut.external_values() {
            let definition = definitions
                .get(value)
                .ok_or("entry-prefix capture has no original definition")?;
            if !dom.dominates(*definition, header) {
                return Err("entry-prefix capture is not available at the original header".into());
            }
        }
        let mut analysis = original.clone();
        let boundary = analysis
            .blocks
            .iter_mut()
            .find(|block| block.id == header)
            .ok_or("entry-prefix missing original header")?;
        let mut stop = boundary
            .body
            .last()
            .cloned()
            .ok_or("entry-prefix empty header")?;
        // Analysis only: preserve the real header ID/parameters, stop before its
        // operations. Semantic consumers reconstruct original instructions and
        // explicitly stop at this boundary with its exact live-ins/arguments.
        stop.inst = Inst::Return { values: vec![] };
        boundary.body = vec![stop];
        let projected = DominatorTree::new(&analysis);
        if !projected.is_well_formed() || !projected.is_reachable(header) {
            return Err("invalid entry-prefix analysis CFG".into());
        }
        let blocks: HashMap<_, _> = analysis
            .blocks
            .iter()
            .filter(|block| projected.is_reachable(block.id))
            .map(|block| (block.id, block))
            .collect();
        let mut degrees: HashMap<_, usize> = blocks.keys().map(|&id| (id, 0)).collect();
        for block in blocks.values() {
            for edge in block
                .terminator()
                .ok_or("entry-prefix missing terminator")?
                .inst
                .successor_edges()
            {
                *degrees
                    .get_mut(&edge.target)
                    .ok_or("entry-prefix dangling successor")? += 1;
            }
        }
        let mut ready: BTreeSet<_> = degrees
            .iter()
            .filter_map(|(&id, &n)| (n == 0).then_some(id))
            .collect();
        let mut order = Vec::new();
        while let Some(id) = ready.pop_first() {
            order.push(id);
            for edge in blocks[&id].terminator().unwrap().inst.successor_edges() {
                let count = degrees.get_mut(&edge.target).unwrap();
                *count -= 1;
                if *count == 0 {
                    ready.insert(edge.target);
                }
            }
        }
        if order.len() != blocks.len() || order.first() != Some(&original.entry) {
            return Err("entry-prefix leaves a cyclic or disconnected residual CFG".into());
        }
        Ok(Self {
            loop_cut,
            analysis,
            order,
        })
    }
    pub fn original(&self) -> &'f Function {
        self.loop_cut.original()
    }
    /// CFG-only, potentially return/signature-invalid; never a semantic endpoint.
    pub fn analysis_function(&self) -> &Function {
        &self.analysis
    }
    pub fn header(&self) -> BlockId {
        self.loop_cut.header()
    }
    /// Exact actual step live-ins, in stable SSA-ID order. A boundary callback
    /// must receive these original definitions as well as the real edge args.
    pub fn boundary_captures(&self) -> &[ValueId] {
        self.loop_cut.external_values()
    }
    pub fn topological_blocks(&self) -> &[BlockId] {
        &self.order
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ModuleBuilder;
    use trust_ir::Ty;
    fn fixture() -> (trust_ir::Module, BlockId, BlockId, ValueId, ValueId) {
        let mut m = ModuleBuilder::new("entry_cut");
        let ty = m.add_func_type(vec![Ty::Bool], vec![Ty::Bool]);
        let mut f = m.function("f", ty);
        let entry = f.create_block();
        let pre = f.create_block();
        let header = f.create_block();
        let body = f.create_block();
        let done = f.create_block();
        let failed = f.create_block();
        let condition = f.add_block_param(entry, Ty::Bool);
        let state = f.add_block_param(header, Ty::Bool);
        let failure = f.add_block_param(failed, Ty::Bool);
        f.switch_to_block(entry);
        f.condbr(condition, pre, vec![], failed, vec![condition]);
        f.switch_to_block(pre);
        f.br(header, vec![condition]);
        f.switch_to_block(header);
        f.condbr(condition, body, vec![], done, vec![]);
        f.switch_to_block(body);
        f.br(header, vec![state]);
        f.switch_to_block(done);
        f.ret(vec![state]);
        f.switch_to_block(failed);
        f.ret(vec![failure]);
        f.build();
        (m.build().unwrap(), header, failed, condition, failure)
    }
    #[test]
    fn entry_prefix_cut_preserves_original_liveins_entry_and_error_exit() {
        let (m, header, failed, condition, _) = fixture();
        let original = &m.functions[0];
        let cut = EntryPrefixCut::new(original, header).unwrap();
        assert!(std::ptr::eq(cut.original(), original));
        assert_eq!(cut.analysis_function().entry, original.entry);
        assert_eq!(cut.boundary_captures(), [condition]);
        assert!(cut.topological_blocks().contains(&failed));
        assert!(cut.topological_blocks().contains(&header));
        assert_eq!(cut.topological_blocks().len(), 4);
        assert!(matches!(
            cut.original()
                .blocks
                .iter()
                .find(|b| b.id == header)
                .unwrap()
                .terminator()
                .unwrap()
                .inst,
            Inst::CondBr { .. }
        ));
        assert!(matches!(
            cut.analysis_function()
                .blocks
                .iter()
                .find(|b| b.id == header)
                .unwrap()
                .terminator()
                .unwrap()
                .inst,
            Inst::Return { .. }
        ));
    }
    #[test]
    fn entry_prefix_cut_rejects_missing_and_foreign_same_typed_capture() {
        let (m, header, _, _, foreign) = fixture();
        for capture in [ValueId(999), foreign] {
            let mut f = m.functions[0].clone();
            let block = f.blocks.iter_mut().find(|b| b.id == header).unwrap();
            let Inst::CondBr { cond, .. } = &mut block.body.last_mut().unwrap().inst else {
                panic!()
            };
            *cond = capture;
            assert!(EntryPrefixCut::new(&f, header).is_err());
        }
    }
    #[test]
    fn entry_prefix_cut_refuses_a_residual_preheader_loop() {
        let mut m = ModuleBuilder::new("entry_cycle");
        let ty = m.add_func_type(vec![Ty::Bool], vec![Ty::Bool]);
        let mut f = m.function("f", ty);
        let entry = f.create_block();
        let before = f.create_block();
        let again = f.create_block();
        let header = f.create_block();
        let body = f.create_block();
        let done = f.create_block();
        let input = f.add_block_param(entry, Ty::Bool);
        let pre = f.add_block_param(before, Ty::Bool);
        let state = f.add_block_param(header, Ty::Bool);
        f.switch_to_block(entry);
        f.br(before, vec![input]);
        f.switch_to_block(before);
        f.condbr(pre, again, vec![], header, vec![pre]);
        f.switch_to_block(again);
        f.br(before, vec![pre]);
        f.switch_to_block(header);
        f.condbr(state, body, vec![], done, vec![]);
        f.switch_to_block(body);
        f.br(header, vec![state]);
        f.switch_to_block(done);
        f.ret(vec![state]);
        f.build();
        let m = m.build().unwrap();
        assert!(NaturalLoopCut::new(&m.functions[0], header).is_ok());
        assert!(EntryPrefixCut::new(&m.functions[0], header).is_err());
    }
}
