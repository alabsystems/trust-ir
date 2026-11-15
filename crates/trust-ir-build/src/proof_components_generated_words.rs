// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Exact word unions: share a surviving input until actual mutation is needed.
//! This changes storage/work only, never which references a summary contains.
use super::Words;
use std::sync::Arc;

#[derive(Clone, Copy, Debug, Default)]
pub(super) struct Statistics {
    pub adopted: usize,
    pub covered: usize,
    pub copied_capacity: usize,
    pub copied_words: usize,
    pub root_lookups_avoided: usize,
}
impl Statistics {
    pub fn include(&mut self, other: Self) {
        self.adopted = self.adopted.saturating_add(other.adopted);
        self.covered = self.covered.saturating_add(other.covered);
        self.copied_capacity = self.copied_capacity.saturating_add(other.copied_capacity);
        self.copied_words = self.copied_words.saturating_add(other.copied_words);
        self.root_lookups_avoided = self
            .root_lookups_avoided
            .saturating_add(other.root_lookups_avoided);
    }
}
enum Storage {
    Owned(Words),
    Shared(Arc<Words>),
}
pub(super) struct Accumulator {
    storage: Storage,
    statistics: Statistics,
}
impl Default for Accumulator {
    fn default() -> Self {
        Self {
            storage: Storage::Owned(Words::new()),
            statistics: Statistics::default(),
        }
    }
}
fn charge(work: &mut usize, limit: usize, amount: usize) -> Result<(), &'static str> {
    let next = work
        .checked_add(amount)
        .filter(|next| *next <= limit)
        .ok_or("generated reference work limit")?;
    *work = next;
    Ok(())
}
fn subset(
    left: &Words,
    right: &Words,
    work: &mut usize,
    limit: usize,
) -> Result<bool, &'static str> {
    if left.len() > right.len() {
        return Ok(false);
    }
    for (&word, &bits) in left {
        charge(work, limit, 1)?;
        if right.get(&word).is_none_or(|stored| bits & !*stored != 0) {
            return Ok(false);
        }
    }
    Ok(true)
}
impl Accumulator {
    pub fn words(&self) -> &Words {
        match &self.storage {
            Storage::Owned(words) => words,
            Storage::Shared(words) => words,
        }
    }
    pub fn requires_header(&self) -> bool {
        matches!(&self.storage, Storage::Owned(_))
    }
    pub fn statistics(&self) -> Statistics {
        self.statistics
    }
    pub fn finish(self) -> Arc<Words> {
        match self.storage {
            Storage::Owned(words) => Arc::new(words),
            Storage::Shared(words) => words,
        }
    }
    fn own(&mut self, work: &mut usize, limit: usize) -> Result<(), &'static str> {
        if let Storage::Shared(words) = &self.storage {
            // Preserve the shared exact input until allocation/copy is paid.
            // Charge retained capacity plus each occupied entry copied; clone
            // preserves the table's hash state rather than rehashing inserts.
            let fee = words
                .capacity()
                .checked_add(words.len())
                .ok_or("generated reference work limit")?;
            charge(work, limit, fee)?;
            let copied = words.as_ref().clone();
            self.statistics.copied_capacity = self
                .statistics
                .copied_capacity
                .saturating_add(words.capacity());
            self.statistics.copied_words = self.statistics.copied_words.saturating_add(words.len());
            self.storage = Storage::Owned(copied);
        }
        Ok(())
    }
    pub fn word(
        &mut self,
        word: u64,
        bits: u64,
        work: &mut usize,
        limit: usize,
    ) -> Result<(), &'static str> {
        charge(work, limit, 1)?;
        match &mut self.storage {
            Storage::Owned(words) => {
                if let Some(stored) = words.get_mut(&word) {
                    let combined = *stored | bits;
                    if combined != *stored {
                        *stored = combined;
                    }
                    return Ok(());
                }
                charge(work, limit, 2)?; // insertion probe and word storage
                words.insert(word, bits);
                Ok(())
            }
            Storage::Shared(words) => {
                if words.get(&word).is_some_and(|stored| bits & !*stored == 0) {
                    return Ok(());
                }
                self.own(work, limit)?;
                self.word(word, bits, work, limit) // real probe of the new table
            }
        }
    }
    pub fn include(
        &mut self,
        incoming: &Arc<Words>,
        work: &mut usize,
        limit: usize,
    ) -> Result<(), &'static str> {
        if incoming.is_empty() {
            return Ok(());
        }
        if self.words().is_empty() {
            charge(work, limit, 1)?; // immutable set pin, no copy/allocation
            self.storage = Storage::Shared(incoming.clone());
            self.statistics.adopted = self.statistics.adopted.saturating_add(1);
            return Ok(());
        }
        if let Storage::Shared(words) = &self.storage {
            charge(work, limit, 1)?;
            if Arc::ptr_eq(words, incoming) {
                self.statistics.covered = self.statistics.covered.saturating_add(1);
                return Ok(());
            }
        }
        // Both probes leave an exact surviving input untouched on failure.
        // Prefer the smaller census, and never allocate for set inclusion.
        let current_first = self.words().len() <= incoming.len();
        let (adopt, covered) = if current_first {
            if subset(self.words(), incoming, work, limit)? {
                (true, false)
            } else {
                (false, subset(incoming, self.words(), work, limit)?)
            }
        } else if subset(incoming, self.words(), work, limit)? {
            (false, true)
        } else {
            (subset(self.words(), incoming, work, limit)?, false)
        };
        if adopt {
            charge(work, limit, 1)?;
            self.storage = Storage::Shared(incoming.clone());
            self.statistics.adopted = self.statistics.adopted.saturating_add(1);
            return Ok(());
        }
        if covered {
            self.statistics.covered = self.statistics.covered.saturating_add(1);
            return Ok(());
        }
        self.own(work, limit)?;
        for (&word, &bits) in incoming.iter() {
            self.word(word, bits, work, limit)?;
        }
        Ok(())
    }
}
impl std::ops::Deref for Accumulator {
    type Target = Words;
    fn deref(&self) -> &Words {
        self.words()
    }
}

#[cfg(test)]
#[path = "proof_components_generated_words_tests.rs"]
mod tests;
