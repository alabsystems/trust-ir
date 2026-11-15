// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        function: &Function,
        summary: &FunctionSummary,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let signature = work.at(&module.func_types, function.ty.index() as usize)?;
        work.admit(8, size_of::<bool>())?;
        let has_clauses = !summary.requires.is_empty()
            || !summary.ensures.is_empty()
            || !summary.decreases.is_empty();
        if (has_clauses || !summary.params.is_empty())
            && let Some(ft) = signature
            && summary.params.len() != ft.params.len()
        {
            work.text("summary lists ", &mut self.detail)?;
            work.number(summary.params.len() as u128, &mut self.detail)?;
            work.text(
                " parameter name(s) but the signature has ",
                &mut self.detail,
            )?;
            work.number(ft.params.len() as u128, &mut self.detail)?;
            self.issue(function, work)?;
        }
        work.admit(1, size_of::<Option<&trust_ir::EffectSummary>>())?;
        if let Some(effects) = &summary.effects {
            work.admit(2, size_of::<[(&str, &EffectSet); 2]>())?;
            for (side, set) in [("reads", &effects.reads), ("writes", &effects.writes)] {
                if !set.is_canonical_observed(work.session, work.site)? {
                    self.side(side, work)?;
                    work.text(" is not canonical: a Places set must be non-empty and strictly ascending (ParamPointee by index, then Global by id, no duplicate); spell the empty set Nothing", &mut self.detail)?;
                    self.issue(function, work)?;
                }
                work.admit(1, size_of::<&[EffectPlace]>())?;
                let places = match set {
                    EffectSet::Places(p) => p.as_slice(),
                    EffectSet::Nothing | EffectSet::Everything => &[],
                };
                let mut index = 0;
                while let Some(place) = work.at(places, index)? {
                    work.admit(1, size_of::<EffectPlace>())?;
                    match place {
                        EffectPlace::ParamPointee { index } => {
                            self.parameter(function, signature, *index, side, work)?
                        }
                        EffectPlace::Global(global) => {
                            if work.at(&module.globals, global.as_usize())?.is_none() {
                                self.side(side, work)?;
                                work.text(" names global #", &mut self.detail)?;
                                work.number(global.index() as u128, &mut self.detail)?;
                                work.text(
                                    ", which this module does not declare",
                                    &mut self.detail,
                                )?;
                                self.issue(function, work)?;
                            }
                        }
                    }
                    work.next(&mut index)?;
                }
            }
        }
        Ok(())
    }
    fn parameter<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        signature: Option<&FuncTy>,
        parameter: u32,
        side: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        if signature.is_some_and(|ft| (parameter as usize) < ft.params.len()) {
            return Ok(());
        }
        self.side(side, work)?;
        work.text(" names the pointee of parameter ", &mut self.detail)?;
        work.number(parameter as u128, &mut self.detail)?;
        match signature {
            Some(ft) => {
                work.text(" but the signature declares ", &mut self.detail)?;
                work.number(ft.params.len() as u128, &mut self.detail)?;
                work.text(" parameter(s)", &mut self.detail)?;
            }
            None => {
                work.text(", but functy.", &mut self.detail)?;
                work.number(function.ty.index() as u128, &mut self.detail)?;
                work.text(" is not declared in this module", &mut self.detail)?;
            }
        }
        self.issue(function, work)
    }
}
