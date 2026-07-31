// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
#![forbid(unsafe_code)]

pub mod ay_batch;
pub mod builder;
pub mod contracts;
pub mod demo;
pub mod satcert;
pub mod validate;

pub use ay_batch::AYBatchBuilder;
pub use builder::{FunctionBuilder, ModuleBuilder, PtrExtent};
pub use contracts::mint_summary_obligations;
pub use validate::{
    CheckedConsumption, ConsumptionRole, GiveBackReport, ModuleValidationReport,
    SourceToSiliconClaim, SourceToSiliconError, ValidationError, certify_identity_lineage_rung,
    certify_module_give_backs, consumption_role, lineage_closed_with_validated_authority,
    validate_changed, validate_function, validate_module, validate_module_report,
    validate_module_report_with_authority, validate_module_with_authority,
    validate_spec_anchor_functions, validate_spec_module_semantics, verify_source_to_silicon,
};
