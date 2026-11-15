// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl Checking {
    pub(super) fn debug<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.definitions(function, work)?;
        self.names(function, work)?;
        self.scopes(function, work)?;
        let scope_count = function.scopes.as_ref().map_or(0, Vec::len);
        for block in &function.blocks {
            work.admit(1, 0)?;
            for (instruction, node) in block.body.iter().enumerate() {
                work.admit(1, 0)?;
                if let Some(scope) = node.scope
                    && (scope as usize) >= scope_count
                {
                    self.fixed(
                        || ValidationError::InvalidInstructionScope {
                            function: function.id.index(),
                            block: block.id.index(),
                            instruction,
                            scope,
                            scope_count,
                        },
                        work,
                    )?;
                }
            }
        }
        Ok(())
    }
    fn definitions<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        for block in &function.blocks {
            work.admit(1, 0)?;
            for (value, _) in &block.params {
                self.definition(value.index(), work)?;
            }
            for node in &block.body {
                work.admit(1, 0)?;
                for value in &node.results {
                    self.definition(value.index(), work)?;
                }
            }
        }
        Ok(())
    }
    pub(super) fn definition<O: ExecutionObserver>(
        &mut self,
        value: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        if !work.contains(&self.definitions, value)? {
            work.push(&mut self.definitions, value)?;
        }
        Ok(())
    }
    fn names<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        if let Some(names) = &function.value_names {
            for (value, _) in names {
                work.admit(1, 0)?;
                let value = value.index();
                if work.contains(&self.names, value)? {
                    self.detail(
                        "the same SSA value appears more than once",
                        |detail| ValidationError::InvalidValueName {
                            function: function.id.index(),
                            value,
                            detail,
                        },
                        work,
                    )?;
                } else {
                    work.push(&mut self.names, value)?;
                    if !work.contains(&self.definitions, value)? {
                        self.detail(
                            "no block parameter or instruction result defines it",
                            |detail| ValidationError::InvalidValueName {
                                function: function.id.index(),
                                value,
                                detail,
                            },
                            work,
                        )?;
                    }
                }
            }
        }
        Ok(())
    }
    fn scopes<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        let Some(scopes) = &function.scopes else {
            return Ok(());
        };
        if scopes.is_empty() {
            self.detail(
                "a present scope table must contain an outermost scope",
                |detail| ValidationError::InvalidScopeTree {
                    function: function.id.index(),
                    scope: 0,
                    detail,
                },
                work,
            )?;
        }
        // Exactly the original u32 nameable prefix, with no truncating cast or
        // permissive cap. The final index, not the count, is what must fit.
        if scopes
            .len()
            .checked_sub(1)
            .is_some_and(|last| u32::try_from(last).is_err())
        {
            self.scope_overflow(function.id.index(), scopes.len(), work)?;
        }
        for (index, scope) in scopes.iter().enumerate() {
            work.admit(1, 0)?;
            let Ok(index) = u32::try_from(index) else {
                break;
            };
            let valid = if index == 0 {
                scope.parent.is_none()
            } else {
                scope.parent.is_some_and(|parent| parent < index)
            };
            if !valid {
                let text = if index == 0 {
                    "the outermost scope must have no parent"
                } else {
                    "every non-root scope must name an earlier parent"
                };
                self.detail(
                    text,
                    |detail| ValidationError::InvalidScopeTree {
                        function: function.id.index(),
                        scope: index,
                        detail,
                    },
                    work,
                )?;
            }
            if let Some(link) = &scope.inlined_at {
                if index == 0 {
                    self.detail("the outermost scope is the function's own body and cannot have been inlined", |detail| ValidationError::InvalidInlinedScope {
                        function: function.id.index(), scope: 0, detail }, work)?;
                }
                work.admit(1, 0)?;
                if link.callee.is_empty() {
                    self.detail(
                        "an inlining chain link must name its callee",
                        |detail| ValidationError::InvalidInlinedScope {
                            function: function.id.index(),
                            scope: index,
                            detail,
                        },
                        work,
                    )?;
                }
            }
        }
        Ok(())
    }
    pub(super) fn scope_overflow<O: ExecutionObserver>(
        &mut self,
        function: u32,
        count: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text("the scope table holds ", &mut self.text)?;
        work.number(count, &mut self.text)?;
        work.text(" entries; a scope past index ", &mut self.text)?;
        work.number(u32::MAX as usize, &mut self.text)?;
        work.text(
            " can be named by nothing (ScopeData.parent and InstrNode.scope are u32)",
            &mut self.text,
        )?;
        self.built_detail(
            |detail| ValidationError::InvalidScopeTree {
                function,
                scope: u32::MAX,
                detail,
            },
            work,
        )
    }
}
