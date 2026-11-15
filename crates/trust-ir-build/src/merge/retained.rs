// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Immutable original-input custody for the canonical merger. A file path or
//! digest never establishes origin. Only an actual retained input and its
//! actual canonical placement receipts can reuse its own recorded file rows.
//! This is unlicensed data custody, never Rust/source/ABI/proof authority.

use std::sync::Arc;

use trust_ir::Module;

use super::{MergeError, MergePolicy, Merger, Remap, len_u32};

/// A module with its immutable original inputs and actual canonical placement
/// history. Distinct calls to `new` create distinct inputs, even for equal
/// modules or equal paths. Clone preserves the same retained custody.
///
/// The module is read-only. Extracting it and wrapping it again loses its
/// placement custody; raw edits cannot masquerade as canonical continuations.
#[derive(Clone, Debug)]
pub struct RetainedImage {
    module: Arc<Module>,
    origins: Vec<Placement>,
}

#[derive(Clone, Debug)]
struct Placement {
    original: Arc<Module>,
    current: Arc<Module>,
    file_ids: Vec<u32>,
    steps: Vec<Step>,
}

#[derive(Clone, Copy, Debug)]
enum Side {
    Destination,
    Source,
}

#[derive(Clone, Debug)]
struct Step {
    receipt: Arc<Receipt>,
    side: Side,
}

#[derive(Debug)]
struct Receipt {
    source: Arc<Module>,
    destination: Arc<Module>,
    result: Arc<Module>,
    remap: Remap,
}

fn stale() -> MergeError {
    MergeError::Malformed {
        table: "retained file placement",
        id: 0,
        detail: "original input, canonical receipt or current immutable image differs",
    }
}

impl RetainedImage {
    /// Retain one actual original input. This validates no semantic, source or
    /// licensing claim. In particular it does not authenticate a Rust instance.
    pub fn new(module: Module) -> Result<Self, MergeError> {
        let count = len_u32(module.files.len(), "files")?;
        let module = Arc::new(module);
        let origin = Placement {
            original: Arc::clone(&module),
            current: Arc::clone(&module),
            file_ids: (0..count).collect(),
            steps: Vec::new(),
        };
        Ok(Self {
            module,
            origins: vec![origin],
        })
    }

    pub fn module(&self) -> &Module {
        &self.module
    }

    /// Extract data only. A later `new` starts a distinct input; it cannot
    /// recover this image's original-input/placement custody from content.
    pub fn into_module(self) -> Module {
        Arc::unwrap_or_clone(self.module)
    }

    fn validate(&self) -> Result<(), MergeError> {
        for placement in &self.origins {
            let mut current = &placement.original;
            let count = len_u32(current.files.len(), "files")?;
            let mut file_ids: Vec<u32> = (0..count).collect();
            for step in &placement.steps {
                let before = match step.side {
                    Side::Destination => &step.receipt.destination,
                    Side::Source => &step.receipt.source,
                };
                if !Arc::ptr_eq(current, before) {
                    return Err(stale());
                }
                if let Side::Source = step.side {
                    file_ids = file_ids
                        .iter()
                        .map(|&file| step.receipt.remap.file(file).ok_or_else(stale))
                        .collect::<Result<_, _>>()?;
                }
                current = &step.receipt.result;
            }
            // These are the EXACT immutable module objects the canonical
            // merger used and produced, not equality of hashes or filenames.
            if !Arc::ptr_eq(current, &self.module)
                || !Arc::ptr_eq(&placement.current, &self.module)
                || file_ids != placement.file_ids
                || file_ids
                    .iter()
                    .any(|&f| f as usize >= self.module.files.len())
            {
                return Err(stale());
            }
        }
        Ok(())
    }

    /// Merge by the existing canonical remapper and all its normal complete
    /// body/license checks. A repeated retained input may reuse ONLY its own
    /// recorded file rows after validating both actual placement histories.
    /// Different inputs and file-less/unknown origins retain ordinary rules.
    /// On error both immutable images remain unchanged.
    pub fn merge(&self, source: &Self, policy: &MergePolicy) -> Result<(Self, Remap), MergeError> {
        self.validate()?;
        source.validate()?;
        let mut reuse = vec![None; source.module.files.len()];
        for incoming in &source.origins {
            let Some(prior) = self
                .origins
                .iter()
                .find(|p| Arc::ptr_eq(&p.original, &incoming.original))
            else {
                continue;
            };
            for (&source_file, &destination_file) in incoming.file_ids.iter().zip(&prior.file_ids) {
                let slot = reuse.get_mut(source_file as usize).ok_or_else(stale)?;
                if slot.is_some_and(|old| old != destination_file) {
                    return Err(stale());
                }
                *slot = Some(destination_file);
            }
        }
        let mut merger = Merger::new(&self.module, &source.module, *policy)?;
        merger.retained_files = Some(reuse);
        let staged = merger.run()?;
        let mut result = self.module.as_ref().clone();
        let remap = staged.commit(&mut result);
        let result = Arc::new(result);
        let receipt = Arc::new(Receipt {
            source: Arc::clone(&source.module),
            destination: Arc::clone(&self.module),
            result: Arc::clone(&result),
            remap: remap.clone(),
        });
        let mut origins: Vec<Placement> = Vec::new();
        for (image, side) in [(self, Side::Destination), (source, Side::Source)] {
            for old in &image.origins {
                let mut placement = old.clone();
                if let Side::Source = side {
                    placement.file_ids = placement
                        .file_ids
                        .iter()
                        .map(|&file| remap.file(file).ok_or_else(stale))
                        .collect::<Result<_, _>>()?;
                }
                placement.current = Arc::clone(&result);
                placement.steps.push(Step {
                    receipt: Arc::clone(&receipt),
                    side,
                });
                if let Some(prior) = origins
                    .iter()
                    .find(|p| Arc::ptr_eq(&p.original, &placement.original))
                {
                    if prior.file_ids != placement.file_ids {
                        return Err(stale());
                    }
                } else {
                    origins.push(placement);
                }
            }
        }
        let output = Self {
            module: result,
            origins,
        };
        output.validate()?;
        Ok((output, remap))
    }
}
