// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn extract<O: ExecutionObserver>(
        &mut self,
        block: u32,
        declared: &Ty,
        array: ValueId,
        index: ValueId,
        values: &ObservedValueTypes,
        constants: &[(u32, i128)],
        module: Option<&Module>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some(array_ty) = values.get_observed(array, work.session, work.site)? else {
            return self.index(
                block,
                "extract_element",
                index,
                None,
                values,
                constants,
                work,
            );
        };
        work.admit(3, 0)?;
        if !matches!(array_ty, Ty::Vector(..) | Ty::Array(..) | Ty::Sequence(_)) {
            self.wrong_kind(block, "extract_element", array_ty, work)?;
            return self.index(
                block,
                "extract_element",
                index,
                None,
                values,
                constants,
                work,
            );
        }
        self.table(
            block,
            "extract_element",
            "result type",
            module,
            array_ty,
            declared,
            work,
        )?;
        work.admit(1, 0)?;
        if let Ty::Vector(lane, _) = array_ty
            && !lane.structural_eq_observed(declared, work.session, work.site)?
            && !consumption(lane, declared, work)?
        {
            self.mismatch(
                block,
                "extract_element",
                "result type must match vector lane type ",
                lane,
                declared,
                work,
            )?;
        }
        self.index(
            block,
            "extract_element",
            index,
            Some(array_ty),
            values,
            constants,
            work,
        )
    }

    pub(super) fn insert<O: ExecutionObserver>(
        &mut self,
        block: u32,
        declared: &Ty,
        array: ValueId,
        index: ValueId,
        value: ValueId,
        values: &ObservedValueTypes,
        constants: &[(u32, i128)],
        module: Option<&Module>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some(array_ty) = values.get_observed(array, work.session, work.site)? else {
            return self.index(
                block,
                "insert_element",
                index,
                None,
                values,
                constants,
                work,
            );
        };
        work.admit(3, 0)?;
        if !matches!(array_ty, Ty::Vector(..) | Ty::Array(..) | Ty::Sequence(_)) {
            self.wrong_kind(block, "insert_element", array_ty, work)?;
            return self.index(
                block,
                "insert_element",
                index,
                None,
                values,
                constants,
                work,
            );
        }
        if !declared.structural_eq_observed(array_ty, work.session, work.site)? {
            self.mismatch(
                block,
                "insert_element",
                "result type must match operand type ",
                array_ty,
                declared,
                work,
            )?;
        }
        work.admit(1, 0)?;
        if let Ty::Vector(lane, _) = array_ty
            && let Some(actual) = values.get_observed(value, work.session, work.site)?
            && !actual.structural_eq_observed(lane, work.session, work.site)?
            && !consumption(actual, lane, work)?
        {
            self.mismatch(
                block,
                "insert_element",
                "inserted value must match vector lane type ",
                lane,
                actual,
                work,
            )?;
        }
        if let Some(actual) = values.get_observed(value, work.session, work.site)? {
            self.table(
                block,
                "insert_element",
                "inserted value",
                module,
                array_ty,
                actual,
                work,
            )?;
        }
        self.index(
            block,
            "insert_element",
            index,
            Some(array_ty),
            values,
            constants,
            work,
        )
    }
}

pub(super) fn consumption<O: ExecutionObserver>(
    actual: &Ty,
    declared: &Ty,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.admit(2, 0)?;
    Ok(matches!(actual, Ty::Refine(..)) || matches!(declared, Ty::Refine(..)))
}
