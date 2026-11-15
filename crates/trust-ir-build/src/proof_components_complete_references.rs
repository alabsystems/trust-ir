// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Complete syntactic FVar summaries for one actual component owner. Unlike
//! scoped capture dependencies, these never subtract ambient IDs or formals.
//! Only retained original declaration types/values publish persistent keys.
//! Temporary caller inputs use the original fresh walk. Owners, original
//! definitions and per-root visibility are checked on every construction;
//! a summary supplies no normalization premise or additional graph lifetime.

use super::NormalizationReferences;
pub(super) use super::reference_memo::{Cache, Scan};
use clean_kernel::{Expr, expr::FVarId};

/// The unrequested path constructs exactly the original fresh walker; it
/// creates no reference-cache maps, summaries or retained graph inventory.
pub(super) enum References<'a> {
    Fresh(NormalizationReferences),
    Reused {
        inputs: NormalizationReferences,
        retained: Scan<'a>,
        retained_started: bool,
    },
}
impl<'a> References<'a> {
    pub(super) fn new(cache: Option<&'a mut Cache>, limit: usize) -> Result<Self, String> {
        match cache {
            Some(cache) => Ok(Self::Reused {
                inputs: NormalizationReferences::new(limit),
                retained: Scan::new(cache, limit)?,
                retained_started: false,
            }),
            None => Ok(Self::Fresh(NormalizationReferences::new(limit))),
        }
    }
    pub(super) fn contains(&mut self, id: FVarId) -> Result<bool, String> {
        match self {
            Self::Fresh(scan) => Ok(scan.contains(id)),
            Self::Reused {
                inputs,
                retained,
                retained_started,
            } => {
                if !*retained_started {
                    retained.reserve_input_work(inputs.work);
                    *retained_started = true;
                }
                if inputs.contains(id) {
                    return Ok(true);
                }
                // The fresh input set supplied the original membership probe.
                // Pay the additional retained-summary query before making it.
                retained.charged_contains(id)
            }
        }
    }
    pub(super) fn scan_input(&mut self, expression: &Expr) -> Result<(), String> {
        match self {
            Self::Fresh(scan) => scan.scan(expression),
            Self::Reused {
                inputs,
                retained,
                retained_started,
            } => {
                if *retained_started {
                    retained.poison();
                    return Err("normalization inputs must precede retained declarations".into());
                }
                let result = inputs.scan(expression);
                if result.is_err() {
                    retained.poison();
                }
                result
            }
        }
    }
    /// The owning constructor supplies only original retained types/values.
    /// Their immutable graphs already live for this component's lifetime.
    pub(super) fn scan_retained(&mut self, expression: &Expr) -> Result<(), String> {
        match self {
            Self::Fresh(scan) => scan.scan(expression),
            Self::Reused {
                inputs,
                retained,
                retained_started,
            } => {
                if !*retained_started {
                    retained.reserve_input_work(inputs.work);
                    *retained_started = true;
                }
                retained.scan(expression)
            }
        }
    }
    pub(super) fn work(&self) -> usize {
        match self {
            Self::Fresh(scan) => scan.work,
            Self::Reused {
                inputs, retained, ..
            } => {
                // The input phase precedes the retained phase, whose limit is
                // reduced by input work. Saturation cannot increase admission.
                inputs.work.saturating_add(retained.work)
            }
        }
    }
}
