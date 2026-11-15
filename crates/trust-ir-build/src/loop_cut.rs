// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! A structural natural-loop cut for independently reconstructed step semantics.
//! The analysis projection is NOT an executable function or a proof certificate.
//! Consumers must validate original typed SSA and give every cut an explicit
//! continuation/observation meaning. No cyclic CFG is admitted by this view.
use std::collections::{BTreeSet, HashMap};
use trust_ir::{BlockId, Function, Inst, ValueId, analysis::DominatorTree};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Backedge {
    pub predecessor: BlockId,
    pub header: BlockId,
    pub arguments: Vec<ValueId>,
}
pub struct NaturalLoopCut<'f> {
    original: &'f Function,
    analysis: Function,
    header: BlockId,
    edges: Vec<Backedge>,
    order: Vec<BlockId>,
    external: Vec<ValueId>,
}
impl<'f> NaturalLoopCut<'f> {
    /// Cut dominated backedges to one real reachable header. A conditional
    /// backedge retains its non-backedge successor in the analysis projection;
    /// the original condition and both argument lists remain semantic inputs.
    /// Irreducible/multiple residual cycles explicitly refuse.
    /// SSA uses/definitions are retained from the original, not the projection.
    pub fn new(original: &'f Function, header: BlockId) -> Result<Self, String> {
        if original.blocks.len() > 65_536 {
            return Err("loop cut block budget".into());
        }
        let dom = DominatorTree::new(original);
        if !dom.is_well_formed() || !dom.is_reachable(header) {
            return Err("loop cut needs a well-formed reachable original header".into());
        }
        let mut analysis = original.clone();
        analysis.entry = header;
        let mut edges = Vec::new();
        for block in &mut analysis.blocks {
            if !dom.is_reachable(block.id) || !dom.dominates(header, block.id) {
                continue;
            }
            let node = block
                .body
                .last_mut()
                .ok_or("loop cut empty original block")?;
            match &node.inst {
                Inst::Br { target, args } if *target == header => {
                    edges.push(Backedge {
                        predecessor: block.id,
                        header,
                        arguments: args.clone(),
                    });
                    // Return is ONLY an analysis sink. Semantic consumers still
                    // read the original Br and interpret its exact arguments.
                    node.inst = Inst::Return {
                        values: args.clone(),
                    };
                }
                Inst::CondBr {
                    then_target,
                    then_args,
                    else_target,
                    else_args,
                    ..
                } if *then_target == header || *else_target == header => {
                    let then_cut = *then_target == header;
                    let else_cut = *else_target == header;
                    if then_cut {
                        edges.push(Backedge {
                            predecessor: block.id,
                            header,
                            arguments: then_args.clone(),
                        });
                    }
                    if else_cut {
                        edges.push(Backedge {
                            predecessor: block.id,
                            header,
                            arguments: else_args.clone(),
                        });
                    }
                    // This projection supplies only reachability/order. A
                    // semantic consumer reads the original CondBr and sends
                    // each header edge to its explicit resume independently.
                    // Do not create synthetic blocks or discard an exit arm.
                    node.inst = if then_cut && else_cut {
                        Inst::Return {
                            values: then_args.clone(),
                        }
                    } else if then_cut {
                        Inst::Br {
                            target: *else_target,
                            args: else_args.clone(),
                        }
                    } else {
                        Inst::Br {
                            target: *then_target,
                            args: then_args.clone(),
                        }
                    };
                }
                _ => {}
            }
        }
        if edges.is_empty() {
            return Err("no dominated backedge at selected header".into());
        }
        let projected = DominatorTree::new(&analysis);
        if !projected.is_well_formed() {
            return Err("invalid loop-cut analysis CFG".into());
        }
        let blocks: HashMap<_, _> = analysis
            .blocks
            .iter()
            .filter(|b| projected.is_reachable(b.id))
            .map(|b| (b.id, b))
            .collect();
        let mut degree: HashMap<_, usize> = blocks.keys().map(|&id| (id, 0)).collect();
        for block in blocks.values() {
            let node = block
                .terminator()
                .ok_or("loop cut block lacks terminator")?;
            for edge in node.inst.successor_edges() {
                *degree
                    .get_mut(&edge.target)
                    .ok_or("loop cut dangling successor")? += 1;
            }
        }
        let mut ready: BTreeSet<_> = degree
            .iter()
            .filter_map(|(&id, &n)| (n == 0).then_some(id))
            .collect();
        let mut order = Vec::new();
        while let Some(id) = ready.pop_first() {
            order.push(id);
            for edge in blocks[&id].terminator().unwrap().inst.successor_edges() {
                let count = degree.get_mut(&edge.target).unwrap();
                *count -= 1;
                if *count == 0 {
                    ready.insert(edge.target);
                }
            }
        }
        if order.len() != blocks.len() || order.first() != Some(&header) {
            return Err("loop cut leaves a cyclic or disconnected residual CFG".into());
        }
        let mut defined = BTreeSet::new();
        let mut used = BTreeSet::new();
        for block in original
            .blocks
            .iter()
            .filter(|b| blocks.contains_key(&b.id))
        {
            defined.extend(block.params.iter().map(|(id, _)| *id));
            for node in &block.body {
                defined.extend(node.results.iter().copied());
                node.inst.visit_value_operands(|id| {
                    used.insert(id);
                });
            }
        }
        let external = used.difference(&defined).copied().collect();
        edges.sort_by_key(|e| e.predecessor);
        Ok(Self {
            original,
            analysis,
            header,
            edges,
            order,
            external,
        })
    }
    pub fn original(&self) -> &'f Function {
        self.original
    }
    /// A CFG-only projection. It may deliberately violate return/signature
    /// typing and must never be emitted, executed or used as an SSA endpoint.
    pub fn analysis_function(&self) -> &Function {
        &self.analysis
    }
    pub fn header(&self) -> BlockId {
        self.header
    }
    /// One record per original edge occurrence, ordered by predecessor and
    /// then by conditional arm (then before else). A conditional with both
    /// arms targeting the header therefore has two records, even if their
    /// arguments are equal. Consumers still read the original terminator.
    pub fn backedges(&self) -> &[Backedge] {
        &self.edges
    }
    pub fn topological_blocks(&self) -> &[BlockId] {
        &self.order
    }
    pub fn external_values(&self) -> &[ValueId] {
        &self.external
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ModuleBuilder;
    use trust_ir::Ty;
    #[test]
    fn natural_loop_cut_preserves_actual_edge_arguments_and_external_values() {
        let mut module = ModuleBuilder::new("cut");
        let ty = module.add_func_type(vec![Ty::Bool], vec![Ty::Bool]);
        let mut f = module.function("f", ty);
        let entry = f.create_block();
        let header = f.create_block();
        let body = f.create_block();
        let done = f.create_block();
        let condition = f.add_block_param(entry, Ty::Bool);
        let state = f.add_block_param(header, Ty::Bool);
        f.switch_to_block(entry);
        f.br(header, vec![condition]);
        f.switch_to_block(header);
        f.condbr(condition, body, vec![], done, vec![]);
        f.switch_to_block(body);
        f.br(header, vec![state]);
        f.switch_to_block(done);
        f.ret(vec![state]);
        f.build();
        let module = module.build().unwrap();
        let cut = NaturalLoopCut::new(&module.functions[0], header).unwrap();
        assert_eq!(
            cut.backedges(),
            [Backedge {
                predecessor: body,
                header,
                arguments: vec![state]
            }]
        );
        assert_eq!(cut.external_values(), [condition]);
        assert_eq!(cut.topological_blocks().len(), 3);
        assert!(matches!(
            cut.original()
                .blocks
                .iter()
                .find(|b| b.id == body)
                .unwrap()
                .terminator()
                .unwrap()
                .inst,
            Inst::Br { .. }
        ));
        assert!(NaturalLoopCut::new(&module.functions[0], entry).is_err());
    }

    #[test]
    fn natural_loop_cut_preserves_a_conditional_backedge_and_its_exit() {
        let mut module = ModuleBuilder::new("conditional_cut");
        let ty = module.add_func_type(vec![Ty::Bool], vec![Ty::Bool]);
        let mut f = module.function("f", ty);
        let entry = f.create_block();
        let header = f.create_block();
        let body = f.create_block();
        let done = f.create_block();
        let condition = f.add_block_param(entry, Ty::Bool);
        let state = f.add_block_param(header, Ty::Bool);
        f.switch_to_block(entry);
        f.br(header, vec![condition]);
        f.switch_to_block(header);
        f.br(body, vec![]);
        f.switch_to_block(body);
        f.condbr(condition, header, vec![state], done, vec![]);
        f.switch_to_block(done);
        f.ret(vec![state]);
        f.build();
        let module = module.build().unwrap();
        let original = &module.functions[0];
        let cut = NaturalLoopCut::new(original, header).unwrap();
        assert_eq!(
            cut.backedges(),
            [Backedge {
                predecessor: body,
                header,
                arguments: vec![state]
            }]
        );
        assert_eq!(cut.external_values(), [condition]);
        assert_eq!(cut.topological_blocks(), [header, body, done]);
        assert!(
            matches!(original.blocks.iter().find(|b| b.id == body).unwrap().terminator().unwrap().inst,
            Inst::CondBr { then_target, else_target, .. } if then_target == header && else_target == done)
        );
        assert!(
            matches!(cut.analysis_function().blocks.iter().find(|b| b.id == body).unwrap().terminator().unwrap().inst,
            Inst::Br { target, .. } if target == done)
        );
    }

    #[test]
    fn conditional_else_cut_retains_exit_arguments_and_external_guard() {
        let mut module = ModuleBuilder::new("else_cut");
        let ty = module.add_func_type(vec![Ty::Bool, Ty::Bool], vec![Ty::Bool]);
        let mut f = module.function("f", ty);
        let entry = f.create_block();
        let header = f.create_block();
        let body = f.create_block();
        let done = f.create_block();
        let condition = f.add_block_param(entry, Ty::Bool);
        let exit_value = f.add_block_param(entry, Ty::Bool);
        let state = f.add_block_param(header, Ty::Bool);
        let returned = f.add_block_param(done, Ty::Bool);
        f.switch_to_block(entry);
        f.br(header, vec![condition]);
        f.switch_to_block(header);
        f.br(body, vec![]);
        f.switch_to_block(body);
        f.condbr(condition, done, vec![exit_value], header, vec![state]);
        f.switch_to_block(done);
        f.ret(vec![returned]);
        f.build();
        let module = module.build().unwrap();
        let before = format!("{:?}", module.functions[0]);
        let cut = NaturalLoopCut::new(&module.functions[0], header).unwrap();
        assert_eq!(cut.external_values(), [condition, exit_value]);
        assert_eq!(
            cut.backedges(),
            [Backedge {
                predecessor: body,
                header,
                arguments: vec![state]
            }]
        );
        assert!(
            matches!(&cut.analysis_function().blocks.iter().find(|b| b.id == body).unwrap().terminator().unwrap().inst,
            Inst::Br { target, args } if *target == done && args == &vec![exit_value])
        );
        assert_eq!(format!("{:?}", cut.original()), before);
        let entry_cut =
            crate::loop_entry_cut::EntryPrefixCut::new(&module.functions[0], header).unwrap();
        assert_eq!(entry_cut.boundary_captures(), [condition, exit_value]);
        assert_eq!(entry_cut.topological_blocks(), [entry, header]);
    }

    #[test]
    fn both_conditional_backedge_arms_keep_their_order_and_arguments() {
        for same_arguments in [false, true] {
            let mut module = ModuleBuilder::new("both_arms");
            let ty = module.add_func_type(vec![Ty::Bool, Ty::Bool], vec![Ty::Bool]);
            let mut f = module.function("f", ty);
            let entry = f.create_block();
            let header = f.create_block();
            let body = f.create_block();
            let condition = f.add_block_param(entry, Ty::Bool);
            let alternate = f.add_block_param(entry, Ty::Bool);
            let state = f.add_block_param(header, Ty::Bool);
            f.switch_to_block(entry);
            f.br(header, vec![condition]);
            f.switch_to_block(header);
            f.br(body, vec![]);
            f.switch_to_block(body);
            let second = if same_arguments { state } else { alternate };
            f.condbr(condition, header, vec![state], header, vec![second]);
            f.build();
            let module = module.build().unwrap();
            let cut = NaturalLoopCut::new(&module.functions[0], header).unwrap();
            let expected_captures = if same_arguments {
                vec![condition]
            } else {
                vec![condition, alternate]
            };
            // The alternate is used only by the removed else edge. Reading
            // the synthetic Return(then_args) would silently lose it.
            assert_eq!(cut.external_values(), expected_captures);
            let prefix =
                crate::loop_entry_cut::EntryPrefixCut::new(&module.functions[0], header).unwrap();
            assert_eq!(prefix.boundary_captures(), expected_captures);
            assert_eq!(
                cut.backedges(),
                [
                    Backedge {
                        predecessor: body,
                        header,
                        arguments: vec![state]
                    },
                    Backedge {
                        predecessor: body,
                        header,
                        arguments: vec![second]
                    },
                ]
            );
            assert_eq!(cut.topological_blocks(), [header, body]);
            assert!(matches!(
                cut.original()
                    .blocks
                    .iter()
                    .find(|b| b.id == body)
                    .unwrap()
                    .terminator()
                    .unwrap()
                    .inst,
                Inst::CondBr { .. }
            ));
        }
    }

    #[test]
    fn natural_loop_cut_refuses_a_second_residual_cycle() {
        let mut module = ModuleBuilder::new("residual_cut");
        let ty = module.add_func_type(vec![Ty::Bool], vec![Ty::Bool]);
        let mut f = module.function("f", ty);
        let entry = f.create_block();
        let header = f.create_block();
        let body = f.create_block();
        let secondary = f.create_block();
        let condition = f.add_block_param(entry, Ty::Bool);
        let state = f.add_block_param(header, Ty::Bool);
        f.switch_to_block(entry);
        f.br(header, vec![condition]);
        f.switch_to_block(header);
        f.condbr(condition, body, vec![], secondary, vec![]);
        f.switch_to_block(body);
        f.br(header, vec![state]);
        f.switch_to_block(secondary);
        f.br(secondary, vec![]);
        f.build();
        let module = module.build().unwrap();
        let error = NaturalLoopCut::new(&module.functions[0], header)
            .err()
            .unwrap();
        assert!(error.contains("cyclic"), "{error}");
    }
}
