// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
pub(super) enum Lanes<'a> {
    Fields(&'a [FieldDef]),
    Types(&'a [Ty]),
}
impl<'a> Lanes<'a> {
    pub(super) fn len<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R<usize> {
        work.admit(1, size_of::<usize>())?;
        Ok(match self {
            Self::Fields(rows) => rows.len(),
            Self::Types(rows) => rows.len(),
        })
    }
    pub(super) fn at<O: ExecutionObserver>(
        &self,
        index: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<&'a Ty>> {
        match self {
            Self::Fields(rows) => Ok(work.at(rows, index)?.map(|row| &row.ty)),
            Self::Types(rows) => work.at(rows, index),
        }
    }
}
pub(super) fn register<'a, O: ExecutionObserver>(
    module: &'a Module,
    ty: &'a Ty,
    work: &mut Work<'_, '_, O>,
) -> R<Option<Lanes<'a>>> {
    work.admit(1, size_of::<Option<Lanes<'a>>>())?;
    Ok(match ty {
        Ty::Struct(id) => {
            lookup::structure(module, *id, work)?.map(|def| Lanes::Fields(&def.fields))
        }
        Ty::Tuple(rows) => Some(Lanes::Types(rows)),
        _ => None,
    })
}
