// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn walk<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        function: &Function,
        summary: &FunctionSummary,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let signature = work.at(&module.func_types, function.ty.index() as usize)?;
        work.admit(1, size_of::<[ContractClauseRole; 3]>())?;
        for role in ContractClauseRole::ALL {
            work.admit(3, size_of::<&[ProofFormula]>())?;
            let clauses = role.clauses(summary);
            let mut index = 0;
            while let Some(clause) = work.at(clauses, index)? {
                if work.blank(&clause.schema)? {
                    clause_prefix(role, index, &mut self.detail, work)?;
                    work.text(" has an empty schema", &mut self.detail)?;
                    self.issue(function, work)?;
                }
                let mut at = 0;
                while let Some((name, binding)) = work.at(&clause.bindings, at)? {
                    if work.blank(name)? {
                        clause_prefix(role, index, &mut self.detail, work)?;
                        work.text(" binds a blank free name, which can never be the name of a variable in the clause",&mut self.detail)?;
                        self.issue(function, work)?;
                    }
                    // Exact raw name identity; repeat prior physical scans
                    // instead of an opaque BTreeSet or cloned names.
                    let mut earlier = 0;
                    let mut duplicate = false;
                    while earlier < at {
                        let (prior, _) = work
                            .at(&clause.bindings, earlier)?
                            .ok_or(ObservedValueError::InvalidRange)?;
                        if work.equal(prior, name)? {
                            duplicate = true;
                            break;
                        }
                        work.next(&mut earlier)?;
                    }
                    if duplicate {
                        binding_prefix(role, index, name, &mut self.detail, work)?;
                        work.text(" is bound more than once; `bindings` is a name -> (sort, place) map, so a repeated name leaves the clause's free variable ambiguous",&mut self.detail)?;
                        self.issue(function, work)?;
                    }
                    self.places(
                        function, summary, signature, role, index, name, binding, work,
                    )?;
                    if typing::check(
                        module,
                        function,
                        role,
                        index,
                        name,
                        binding,
                        &mut self.values,
                        &mut self.detail,
                        &mut self.render,
                        work,
                    )? {
                        self.issue(function, work)?;
                    }
                    work.next(&mut at)?;
                }
                work.next(&mut index)?;
            }
        }
        Ok(())
    }
}
/// Every actual parameter/result definition is observed; membership is raw
/// u32 equality. No set/map construction or instruction/type inference is
/// hidden behind this query, including after an early matching definition.
pub(super) fn defined<O: ExecutionObserver>(
    function: &Function,
    value: ValueId,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(1, size_of::<bool>())?;
    let mut found = false;
    let mut at = 0;
    while let Some(block) = work.at(&function.blocks, at)? {
        let mut index = 0;
        while let Some((id, _)) = work.at(&block.params, index)? {
            work.admit(1, 2 * size_of::<u32>())?;
            found |= id.index() == value.index();
            work.next(&mut index)?;
        }
        let mut index = 0;
        while let Some(node) = work.at(&block.body, index)? {
            let mut result = 0;
            while let Some(id) = work.at(&node.results, result)? {
                work.admit(1, 2 * size_of::<u32>())?;
                found |= id.index() == value.index();
                work.next(&mut result)?;
            }
            work.next(&mut index)?;
        }
        work.next(&mut at)?;
    }
    work.admit(1, size_of::<bool>())?;
    Ok(found)
}
