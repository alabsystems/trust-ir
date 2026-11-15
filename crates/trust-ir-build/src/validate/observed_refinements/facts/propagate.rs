// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::super::graph::{self, Flow};
use super::*;
impl<'a> Flow<'a> {
    pub(in super::super) fn propagate<O: ExecutionObserver>(
        &mut self,
        state: &mut State<'a>,
        module: &'a Module,
        function: &'a Function,
        signature: Option<&FuncTy>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.incoming(function, work)?;
        self.order(function, work)?;
        let mut oi = 0;
        while oi < self.order.len() {
            work.admit(1, size_of::<u32>())?;
            let block_id = self.order[oi];
            oi += 1;
            let Some(block) = graph::block(function, block_id, work)? else {
                continue;
            };
            if block.id == function.entry {
                if let Some(sig) = signature {
                    for (i, (vid, _)) in block.params.iter().enumerate() {
                        work.admit(1, 0)?;
                        let d = declared(module, work.at(&sig.params, i)?, work)?;
                        if !self.facts.view(module, d, work)?.top() {
                            self.set(vid.index(), d, work)?;
                        }
                    }
                }
            } else {
                for (i, (vid, _)) in block.params.iter().enumerate() {
                    work.admit(1, size_of::<(Option<Fact>, bool)>())?;
                    let mut joined = None;
                    let mut complete = true;
                    let mut found = false;
                    for ei in 0..self.incoming.len() {
                        work.admit(1, 0)?;
                        let (target, args) = self.incoming[ei];
                        if target != block_id {
                            continue;
                        }
                        found = true;
                        let Some(arg) = work.at(args, i)?.copied() else {
                            complete = false;
                            break;
                        };
                        if !graph::contains(&self.available, arg.index(), work)? {
                            complete = false;
                            break;
                        }
                        let fact = self.assumed(module, arg, work)?;
                        joined = Some(match joined {
                            None => fact,
                            Some(acc) => self.facts.join(module, acc, fact, work)?,
                        });
                    }
                    if found
                        && complete
                        && let Some(j) = joined
                        && !self.facts.view(module, j, work)?.top()
                    {
                        self.set(vid.index(), j, work)?;
                    }
                }
            }
            for (vid, _) in &block.params {
                work.admit(1, 0)?;
                graph::insert(&mut self.available, vid.index(), work)?;
            }
            for node in &block.body {
                work.admit(1, 0)?;
                if node.results.len() == 1 {
                    let result = node.results[0];
                    // One exact representation peel. The owned value map remains
                    // live while the borrowed carrier is used by derivation.
                    let representation = match self.value(result, work)? {
                        Some(Ty::Refine(base, _)) => work.at(&module.types, base.as_usize())?,
                        other => other,
                    };
                    // Preserve ABSENT versus PRESENT-with-unknown-range: only the
                    // former falls back to the instruction's declared result type.
                    let repr = representation.map(trust_ir::propagate::integer_value_range);
                    let d = self.derive(module, &node.inst, repr, work)?;
                    if !self.facts.view(module, d, work)?.top() {
                        let declared = declared(module, self.value(result, work)?, work)?;
                        if !self.facts.view(module, declared, work)?.top() {
                            let a = self.facts.view(module, declared, work)?;
                            let b = self.facts.view(module, d, work)?;
                            let contradiction =
                                if matches!(a, View::Bottom) || matches!(b, View::Bottom) {
                                    false
                                } else {
                                    match (
                                        lattice::bounds(module, a, 0, work)?,
                                        lattice::bounds(module, b, 0, work)?,
                                    ) {
                                        (Some((al, ah)), Some((bl, bh))) => ah < bl || bh < al,
                                        _ => false,
                                    }
                                };
                            if contradiction {
                                state.clear_location(work);
                                work.text("function '", &mut state.location)?;
                                work.text(&function.name, &mut state.location)?;
                                work.text("' bb", &mut state.location)?;
                                work.number(block_id as u128, &mut state.location)?;
                                work.text(": %", &mut state.location)?;
                                work.number(result.index() as u128, &mut state.location)?;
                                work.describe_view(module, a, &mut state.actual)?;
                                work.describe_view(module, b, &mut state.required)?;
                                state.commit(ErrorKind::Contradicted, Sink::Main, work)?;
                            }
                        }
                        self.set(result.index(), d, work)?;
                    }
                }
                for result in &node.results {
                    work.admit(1, 0)?;
                    graph::insert(&mut self.available, result.index(), work)?;
                }
            }
            graph::insert(&mut self.visited_blocks, block_id, work)?;
        }
        Ok(())
    }
}
