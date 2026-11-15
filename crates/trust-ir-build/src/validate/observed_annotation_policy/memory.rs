// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
// Already in ordinary lexicographic order, independent of input role order.
pub(super) const ROLES: [&str; 3] = ["append_only_buffer", "atomic_set_insert", "readonly_table"];
fn roles<O: ExecutionObserver>(proofs: &[ProofAnnotation], work: &mut Work<'_, '_, O>) -> R<u8> {
    let mut found = 0u8;
    for proof in proofs {
        work.admit(4, 0)?;
        let bit = match proof {
            ProofAnnotation::AppendOnlyBuffer => 1,
            ProofAnnotation::AtomicSetInsert => 2,
            ProofAnnotation::ReadonlyTable => 4,
            // Preserve automatic refusal if a future actual memory role has
            // no reviewed spelling here, rather than silently ignoring it.
            other if other.is_memory_role() => return Err(ObservedValueError::UnsupportedValue),
            _ => 0,
        };
        found |= bit;
    }
    Ok(found)
}
impl Checking {
    pub(super) fn memory<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let found = roles(&function.proofs, work)?;
        if found.count_ones() > 1 {
            self.role_text(found, work)?;
            work.text(&function.name, &mut self.name)?;
            work.admit(1, size_of::<ValidationError>())?;
            self.pending = Some(ValidationError::ConflictingFunctionMemoryRoles {
                func_name: take(&mut self.name),
                roles: take(&mut self.roles),
            });
            self.commit(work)?;
        }
        for block in &function.blocks {
            work.admit(1, 0)?;
            for node in &block.body {
                work.admit(1, 0)?;
                let found = roles(&node.proofs, work)?;
                if found.count_ones() > 1 {
                    self.role_text(found, work)?;
                    work.admit(1, size_of::<ValidationError>())?;
                    self.pending = Some(ValidationError::ConflictingMemoryRoles {
                        block: block.id.index(),
                        value: node.results.first().map(|value| value.index()),
                        roles: take(&mut self.roles),
                    });
                    self.commit(work)?;
                }
            }
        }
        Ok(())
    }
    pub(super) fn role_text<O: ExecutionObserver>(
        &mut self,
        found: u8,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        for (index, role) in ROLES.iter().enumerate() {
            work.admit(1, 0)?;
            if found & (1 << index) == 0 {
                continue;
            }
            work.text(role, &mut self.text)?;
            work.reserve(&mut self.roles)?;
            work.admit(1, size_of::<String>())?;
            self.roles.push(take(&mut self.text));
        }
        Ok(())
    }
}
