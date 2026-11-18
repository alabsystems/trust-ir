// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Symbolic nominal field extraction using retained input admission. These
//! candidates preserve the actual fetched evaluator and its complete guards;
//! neither catalog metadata nor a Rust proof wrapper is execution authority.

use super::*;

pub struct ExtractFieldPremises {
    pub aggregate: Expr,
    /// Actual nominal field types. Their exact layout lookup remains a kernel
    /// conversion obligation, not a caller-supplied interpretation certificate.
    pub field_types: Vec<Expr>,
    pub admitted: PendingEquality,
    pub selected: PendingEquality,
}

fn joined(left: PendingEquality, right: PendingEquality) -> PendingEquality {
    PendingEquality::candidate(
        constant("Bool"),
        app("Bool.and", [left.left.clone(), right.left.clone()]),
        constant("Bool.true"),
        app(
            "ir_byte_world_and_intro_v1",
            [left.left, right.left, left.term, right.term],
        ),
    )
}

/// The canonical operand catalog is data. Every selected row and its uniqueness
/// are still checked by the metadata law and final fetched rule at replay.
fn aggregate_type(rows: &Expr, source: &Expr, cap: usize) -> Result<Expr> {
    let mut cursor = rows.clone();
    let mut count = 0;
    let mut found = None;
    loop {
        let head = cursor.get_app_fn();
        if head == &constant("IRList.nil") {
            let fields = cursor.get_app_args();
            if fields.len() != 1 || fields[0] != &constant("IRByteOperandV1") {
                return Err("field extraction operand catalog nil type/shape".into());
            }
            break;
        }
        if count >= cap {
            return Err("field extraction operand catalog construction cap".into());
        }
        count += 1;
        let fields = cursor.get_app_args();
        if head != &constant("IRList.cons")
            || fields.len() != 3
            || fields[0] != &constant("IRByteOperandV1")
        {
            return Err("field extraction operand catalog cons type/shape".into());
        }
        let row = fields[1];
        let row_fields = row.get_app_args();
        if row.get_app_fn() != &constant("IRByteOperandV1.mk") || row_fields.len() != 2 {
            return Err("field extraction operand row shape".into());
        }
        if row_fields[0] == source {
            if found.is_some() {
                return Err("field extraction operand catalog repeats actual source".into());
            }
            found = Some((*row_fields[1]).clone());
        }
        let next = (*fields[2]).clone();
        drop(row_fields);
        drop(fields);
        cursor = next;
    }
    found.ok_or_else(|| "field extraction operand catalog lacks actual source".into())
}

impl FetchedSite {
    /// Derive the actual field evaluator's result from existing aggregate and
    /// selected-lane admission. No new outer premise or alternate evaluator is
    /// introduced: all catalog/layout/value/SSA equations survive kernel replay.
    pub fn extract_field(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        current: &Current,
        value: Expr,
        premises: ExtractFieldPremises,
    ) -> Result<PendingEquality> {
        assembler.charge()?;
        require_same(&self.context, model.context(), "field extraction context")?;
        if premises.field_types.len() > assembler.limits.max_list_items {
            return Err("field extraction nominal field construction cap".into());
        }
        let instruction = self.instruction.get_app_args();
        if self.instruction.get_app_fn() != &constant("IRInst.extractfield")
            || instruction.len() != 3
        {
            return Err("field extraction requires actual ExtractField".into());
        }
        let field_ty = (*instruction[0]).clone();
        let source = (*instruction[1]).clone();
        let index = (*instruction[2]).clone();
        let site = self.site.get_app_args();
        if self.site.get_app_fn() != &constant("IRByteSiteV1.mkt") || site.len() != 7 {
            return Err("field extraction requires actual typed operand catalog".into());
        }
        for (actual, expected) in site[..3].iter().zip([
            nat(u64::from(self.coordinate.function.index())),
            nat(u64::from(self.coordinate.block.index())),
            nat(u64::try_from(self.coordinate.instruction).map_err(|_| "field PC overflow")?),
        ]) {
            require_same(actual, &expected, "field extraction site coordinate")?;
        }
        let aggregate_ty = aggregate_type(site[6], &source, assembler.limits.max_list_items)?;
        let aggregate = premises.aggregate.get_app_args();
        if premises.aggregate.get_app_fn() != &constant("IRScalar.aggv") || aggregate.len() != 1 {
            return Err("field extraction requires complete aggregate scalar".into());
        }
        let spine = (*aggregate[0]).clone();
        drop(aggregate);
        let aggregate_scalar = premises.aggregate.clone();
        let fit = |ty: Expr, scalar: Expr| {
            app(
                "ir_byte_value_matches_v1",
                [model.context().clone(), ty, scalar],
            )
        };
        premises.admitted.endpoints(
            &constant("Bool"),
            &fit(aggregate_ty.clone(), premises.aggregate.clone()),
            &constant("Bool.true"),
        )?;
        premises.selected.endpoints(
            &constant("Bool"),
            &fit(field_ty.clone(), value.clone()),
            &constant("Bool.true"),
        )?;
        let types = list("IRTy", &premises.field_types);
        let layout_unique = assembler.conversion(
            constant("Bool"),
            app(
                "ir_byte_field_layouts_unique_v1",
                [app("ir_byte_context_layouts_v1", [model.context().clone()])],
            ),
            constant("Bool.true"),
        )?;
        let enums_valid = assembler.conversion(
            constant("Bool"),
            app(
                "ir_byte_enum_catalog_valid_v1",
                [app("ir_byte_context_enums_v1", [model.context().clone()])],
            ),
            constant("Bool.true"),
        )?;
        let complete = joined(layout_unique, joined(enums_valid, premises.admitted));
        let types_found = assembler.conversion(
            app("IROption", [app("IRList", [constant("IRTy")])]),
            app(
                "ir_byte_field_types_v1",
                [model.context().clone(), aggregate_ty.clone(), spine.clone()],
            ),
            app(
                "IROption.some",
                [app("IRList", [constant("IRTy")]), types.clone()],
            ),
        )?;
        let lane_found = assembler.conversion(
            app("IROption", [constant("IRTy")]),
            app("ir_byte_field_ty_at_v1", [types.clone(), index.clone()]),
            some("IRTy", field_ty.clone()),
        )?;
        let nominal = assembler.conversion(
            constant("Bool"),
            app("ir_byte_ty_eq_v1", [field_ty.clone(), field_ty.clone()]),
            constant("Bool.true"),
        )?;
        let value_found = assembler.conversion(
            app("IROption", [constant("IRScalar")]),
            app("ir_vals_get", [spine.clone(), index.clone()]),
            some("IRScalar", value.clone()),
        )?;
        let typed = app(
            "ir_byte_extract_typed_v1",
            [
                model.context().clone(),
                aggregate_ty.clone(),
                field_ty.clone(),
                aggregate_scalar.clone(),
                index.clone(),
            ],
        );
        let expected = app("IRStepResult.value", [value.clone()]);
        let selected = PendingEquality::candidate(
            constant("IRStepResult"),
            typed.clone(),
            expected,
            app(
                "ir_byte_field_selected_extract_v1",
                [
                    model.context().clone(),
                    aggregate_ty.clone(),
                    field_ty.clone(),
                    field_ty.clone(),
                    spine,
                    index.clone(),
                    types,
                    value.clone(),
                    complete.term,
                    types_found.term,
                    lane_found.term,
                    nominal.term,
                    value_found.term,
                    premises.selected.term,
                ],
            ),
        );
        let site_valid = app(
            "ir_byte_field_site_valid_v1",
            [
                model.context().clone(),
                self.site.clone(),
                (*site[6]).clone(),
                field_ty.clone(),
            ],
        );
        let valid = if let Some(unique) = assembler.site_catalog_uniqueness(model)? {
            let local_guard = app(
                "Bool.and",
                [
                    app("ir_byte_operands_unique_v1", [(*site[6]).clone()]),
                    app(
                        "ir_byte_ty_list_eq_v1",
                        [
                            app("ir_byte_site_results_v1", [self.site.clone()]),
                            list("IRTy", std::slice::from_ref(&field_ty)),
                        ],
                    ),
                ],
            );
            let local = assembler.conversion(
                constant("Bool"),
                local_guard.clone(),
                constant("Bool.true"),
            )?;
            let combined = joined(unique, local);
            assembler.charge()?;
            PendingEquality::candidate(
                constant("Bool"),
                site_valid,
                constant("Bool.true"),
                Expr::apps(
                    super::field_site_valid::closed_candidate(),
                    [
                        model.context().clone(),
                        self.site.clone(),
                        (*site[6]).clone(),
                        field_ty.clone(),
                        combined.term,
                    ],
                ),
            )
        } else {
            assembler.conversion(constant("Bool"), site_valid, constant("Bool.true"))?
        };
        let aggregate_found = assembler.conversion(
            app("IROption", [constant("IRTy")]),
            app(
                "ir_byte_operand_find_v1",
                [(*site[6]).clone(), source.clone()],
            ),
            some("IRTy", aggregate_ty.clone()),
        )?;
        let known = app(
            "ir_byte_extract_field_v1",
            [
                model.context().clone(),
                self.site.clone(),
                field_ty.clone(),
                source,
                aggregate_scalar.clone(),
                index.clone(),
            ],
        );
        let mut arguments = vec![model.context().clone()];
        arguments.extend(site.iter().map(|field| (*field).clone()));
        arguments.extend([
            field_ty,
            aggregate_ty,
            (*instruction[1]).clone(),
            aggregate_scalar.clone(),
        ]);
        arguments.extend([index, valid.term, aggregate_found.term]);
        let metadata = PendingEquality::candidate(
            constant("IRStepResult"),
            known,
            typed,
            app("ir_byte_field_extract_mkt_v1", arguments),
        );
        let result = assembler.compose(metadata, selected)?;
        // Retain the WHOLE actual SSA read, not merely observational equality
        // of two field evaluators. In particular changing an unselected lane
        // cannot conceal a stale value table behind the same selected result.
        let checks = self.scalar_checks(model, current, value)?;
        let input = assembler.conversion(
            constant("IRScalar"),
            app("ir_getd", [current.machine(), (*instruction[1]).clone()]),
            aggregate_scalar,
        )?;
        // This direct function owns no fresh scoped local or retained cache.
        // Its raw lambda only supplies the scalar argument to the exact
        // fetched nominal evaluator, with every other argument unchanged.
        let function = Expr::lam(
            clean_kernel::BinderInfo::Default,
            constant("IRScalar"),
            app(
                "ir_byte_extract_field_v1",
                [
                    model.context().clone(),
                    self.site.clone(),
                    (*instruction[0]).clone(),
                    (*instruction[1]).clone(),
                    Expr::bvar(0),
                    (*instruction[2]).clone(),
                ],
            ),
        );
        let lifted = assembler.congruence_function(input, constant("IRStepResult"), function)?;
        let begin = assembler.conversion(
            constant("IRStepResult"),
            checks.evaluation,
            lifted.left.clone(),
        )?;
        let end = assembler.conversion(
            constant("IRStepResult"),
            lifted.right.clone(),
            result.left.clone(),
        )?;
        let input = assembler.compose(begin, lifted)?;
        let input = assembler.compose(input, end)?;
        assembler.compose(input, result)
    }
}

#[cfg(test)]
#[path = "core_execution_field_tests.rs"]
mod tests;
