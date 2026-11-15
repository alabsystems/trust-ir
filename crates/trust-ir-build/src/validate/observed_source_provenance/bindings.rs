// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<'f> State<'f> {
    pub(super) fn bindings<O: ExecutionObserver>(
        &mut self,
        id: u32,
        source: &'f SourceLoopProvenance,
        entry: Option<&trust_ir::Block>,
        header: &trust_ir::Block,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(2, 0)?;
        if self.local_hir.capacity() != 0 || self.local_places.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        let mut prior: Option<&str> = None;
        let mut index = 0usize;
        loop {
            work.admit(1, size_of::<&trust_ir::SourceBindingProvenance>())?;
            let Some(binding) = source.bindings.get(index) else {
                return Ok(());
            };
            if work.blank(&binding.name)? {
                self.blank_binding(id, source.source_loop_id, work)?;
            }
            if let Some(prior) = prior
                && work.compare(prior, &binding.name)? != core::cmp::Ordering::Less
            {
                self.unsorted(id, source.source_loop_id, &binding.name, work)?;
            }
            prior = Some(&binding.name);
            if !work.insert(&mut self.local_hir, binding.hir_local_id)? {
                self.duplicate_binding_hir(id, source.source_loop_id, binding.hir_local_id, work)?;
            }
            if !work.insert(&mut self.local_places, binding.place)? {
                self.duplicate_place(id, source.source_loop_id, binding.place, work)?;
            }
            work.admit(2, size_of::<Place>())?;
            let place = match binding.place {
                SourcePlace::FunctionParameter { index } => {
                    if entry.is_none_or(|block| index as usize >= block.params.len()) {
                        self.missing_parameter(id, &binding.name, index, None, work)?;
                    }
                    (0, 0, index)
                }
                SourcePlace::LoopParameter { index } => {
                    if index as usize >= header.params.len() {
                        self.missing_parameter(
                            id,
                            &binding.name,
                            index,
                            Some(source.header.index()),
                            work,
                        )?;
                    }
                    (1, source.source_loop_id, index)
                }
            };
            self.global_binding(id, binding.hir_local_id, &binding.name, place, work)?;
            index = index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
    }
    fn global_binding<O: ExecutionObserver>(
        &mut self,
        id: u32,
        hir: u32,
        name: &'f str,
        place: Place,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0usize;
        let mut found = false;
        loop {
            work.admit(1, size_of::<(u32, &str, Place)>())?;
            let Some((key, old_name, old_place)) = self.global_names.get(index).copied() else {
                break;
            };
            if key == hir {
                found = true;
                let different = work.compare(old_name, name)? != core::cmp::Ordering::Equal;
                let different = if different {
                    true
                } else {
                    work.admit(3, 0)?;
                    old_place != place
                };
                if different {
                    self.inconsistent(id, hir, name, place, work)?;
                }
                break;
            }
            index = index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
        if !found {
            work.reserve(&mut self.global_names)?;
            work.admit(1, size_of::<(u32, &str, Place)>())?;
            self.global_names.push((hir, name, place));
        }
        let mut index = 0usize;
        let mut found = false;
        loop {
            work.admit(4, size_of::<(Place, u32)>())?;
            let Some((key, old_hir)) = self.global_places.get(index).copied() else {
                break;
            };
            if key == place {
                found = true;
                if old_hir != hir {
                    self.ambiguous(id, place, old_hir, hir, work)?;
                }
                break;
            }
            index = index
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
        if !found {
            work.reserve(&mut self.global_places)?;
            work.admit(1, size_of::<(Place, u32)>())?;
            self.global_places.push((place, hir));
        }
        Ok(())
    }
}
