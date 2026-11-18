// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Candidate initialization of the actual byte evaluator, including its
//! initial world-validity obligation. No assumed running state, fresh-owner
//! constant or native entry permission is introduced by these adapters.

use super::*;
use crate::core_reflection::CoreLogicalEntryProfileV1;

/// One actual entry's independently looked-up body, binding and signature.
/// Construction does not assert that supplied arguments or memory are valid.
#[derive(Clone)]
pub struct EntryTarget {
    target: CallTarget,
    function: Expr,
}

/// Coherent initialization candidates. `equality` starts at actual
/// `ir_byte_init_v1`; `valid` is derived for precisely `current`. Neither is
/// a checked fact until the consumer replays its independently closed claim.
pub struct Initialization {
    equality: PendingEquality,
    current: Current,
    valid: PendingEquality,
}

impl Initialization {
    pub fn equality(&self) -> &PendingEquality {
        &self.equality
    }

    pub fn current(&self) -> &Current {
        &self.current
    }

    pub fn valid(&self) -> &PendingEquality {
        &self.valid
    }
}

impl Catalog<'_, '_> {
    /// Select an actual local body without fetching an instruction or scanning
    /// its CFG. Body discovery shares the cache used by ordinary fetched steps.
    /// The current byte profile rejects module globals at initialization.
    pub fn entry(&mut self, fid: FuncId) -> Result<EntryTarget> {
        if !self.reflected.module().globals.is_empty() {
            return Err("byte initialization does not admit module globals".into());
        }
        Ok(EntryTarget {
            target: self.call_target(fid)?,
            function: self.function(fid)?,
        })
    }
}

/// Actual Rust U64 leaf catalog selection, not a checked execution or ABI token.
#[derive(Clone)]
pub struct RustU64EntryV1(EntryTarget);

impl Catalog<'_, '_> {
    pub fn rust_u64_entry_v1(&mut self, fid: FuncId) -> Result<RustU64EntryV1> {
        if self.reflected.logical_entry_profile() != CoreLogicalEntryProfileV1::RustU64LeafV1 {
            return Err("Rust logical entry requires the named actual-module profile".into());
        }
        Ok(RustU64EntryV1(self.entry(fid)?))
    }
}

impl RustU64EntryV1 {
    pub fn admission(&self, model: &MachineModel, arguments: Expr) -> Result<Expr> {
        self.0
            .admission_with_profile(model, arguments, CoreLogicalEntryProfileV1::RustU64LeafV1)
    }
    /// Candidate for the separately named logical Rust initializer. Actual
    /// signature/body/catalog and all pre-memory/value checks remain required.
    pub fn initialize(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        arguments: Expr,
        memory: Expr,
        host: Expr,
        initial_memory: PendingEquality,
        admitted: PendingEquality,
    ) -> Result<Initialization> {
        self.0.initialize_with_profile(
            assembler,
            model,
            arguments,
            memory,
            host,
            initial_memory,
            admitted,
            CoreLogicalEntryProfileV1::RustU64LeafV1,
        )
    }
}

/// Actual Rust U64 addition catalog selection, not a checked execution or ABI token.
#[derive(Clone)]
pub struct RustU64AdditionEntryV1(EntryTarget);

impl Catalog<'_, '_> {
    pub fn rust_u64_add_literal_entry_v1(&mut self, fid: FuncId) -> Result<RustU64AdditionEntryV1> {
        if self.reflected.logical_entry_profile() != CoreLogicalEntryProfileV1::RustU64AddLiteralV1
        {
            return Err("Rust logical entry requires the named actual-module profile".into());
        }
        Ok(RustU64AdditionEntryV1(self.entry(fid)?))
    }
}

impl RustU64AdditionEntryV1 {
    pub fn admission(&self, model: &MachineModel, arguments: Expr) -> Result<Expr> {
        self.0.admission_with_profile(
            model,
            arguments,
            CoreLogicalEntryProfileV1::RustU64AddLiteralV1,
        )
    }
    /// Candidate for the separately named logical Rust initializer. Actual
    /// signature/body/catalog and all pre-memory/value checks remain required.
    pub fn initialize(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        arguments: Expr,
        memory: Expr,
        host: Expr,
        initial_memory: PendingEquality,
        admitted: PendingEquality,
    ) -> Result<Initialization> {
        self.0.initialize_with_profile(
            assembler,
            model,
            arguments,
            memory,
            host,
            initial_memory,
            admitted,
            CoreLogicalEntryProfileV1::RustU64AddLiteralV1,
        )
    }
}

impl EntryTarget {
    /// Exact pre-memory predicate used by actual initialization. Historical
    /// retired allocations remain present and participate in fresh-owner choice.
    pub fn memory_admission(memory: Expr) -> Expr {
        app(
            "ir_byte_memory_owners_v1",
            [
                memory.clone(),
                list("Nat", &[]),
                app("ir_byte_fresh_owner_v1", [memory]),
            ],
        )
    }

    /// Expose the actual local/non-vararg/convention/arity/value guard, not its
    /// truth. It has no result-lane requirement: a void wrapper and a general
    /// result-producing entry use the same byte initialization semantics.
    pub fn admission(&self, model: &MachineModel, arguments: Expr) -> Result<Expr> {
        self.admission_with_profile(model, arguments, CoreLogicalEntryProfileV1::CFastV1)
    }

    fn admission_with_profile(
        &self,
        model: &MachineModel,
        arguments: Expr,
        profile: CoreLogicalEntryProfileV1,
    ) -> Result<Expr> {
        require_same(
            &self.target.context,
            model.context(),
            "entry module context",
        )?;
        let and = |a, b| app("Bool.and", [a, b]);
        let not = |a| app("Bool.not", [a]);
        let length = |ty, values| app("ir_byte_length_v1", [constant(ty), values]);
        let convention = app(
            match profile {
                CoreLogicalEntryProfileV1::CFastV1 => "ir_nat_leb",
                CoreLogicalEntryProfileV1::RustU64LeafV1
                | CoreLogicalEntryProfileV1::RustU64AddLiteralV1 => "ir_nat_eqb",
            },
            [
                app("ir_byte_binding_cc_v1", [self.target.binding.clone()]),
                nat(match profile {
                    CoreLogicalEntryProfileV1::CFastV1 => 1,
                    CoreLogicalEntryProfileV1::RustU64LeafV1
                    | CoreLogicalEntryProfileV1::RustU64AddLiteralV1 => 3,
                }),
            ],
        );
        let guard = and(
            not(app(
                "ir_byte_binding_import_v1",
                [self.target.binding.clone()],
            )),
            and(
                not(app(
                    "ir_byte_signature_vararg_v1",
                    [self.target.signature.clone()],
                )),
                and(
                    convention,
                    and(
                        app(
                            "ir_nat_eqb",
                            [
                                length("Nat", app("ir_func_params", [self.function.clone()])),
                                length("IRScalar", arguments.clone()),
                            ],
                        ),
                        app(
                            "ir_byte_values_match_v1",
                            [
                                model.context().clone(),
                                app(
                                    "ir_byte_signature_params_v1",
                                    [self.target.signature.clone()],
                                ),
                                arguments,
                            ],
                        ),
                    ),
                ),
            ),
        );
        Ok(match profile {
            CoreLogicalEntryProfileV1::CFastV1 => guard,
            CoreLogicalEntryProfileV1::RustU64LeafV1
            | CoreLogicalEntryProfileV1::RustU64AddLiteralV1 => {
                let u64s = list("IRTy", &[app("IRTy.uint_", [nat(64)])]);
                and(
                    app(
                        "ir_byte_ty_list_eq_v1",
                        [
                            app(
                                "ir_byte_signature_params_v1",
                                [self.target.signature.clone()],
                            ),
                            u64s.clone(),
                        ],
                    ),
                    and(
                        app(
                            "ir_byte_ty_list_eq_v1",
                            [
                                app(
                                    "ir_byte_signature_returns_v1",
                                    [self.target.signature.clone()],
                                ),
                                u64s,
                            ],
                        ),
                        guard,
                    ),
                )
            }
        })
    }

    /// Compose real catalog lookups and the caller's exact preconditions into
    /// actual initialization and independently derived starting-world validity.
    /// `initial_memory` is an equality for [`Self::memory_admission`], not a
    /// successful init/allocation premise. The six shared initialization laws
    /// must be present in the consuming kernel environment at final replay.
    pub fn initialize(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        arguments: Expr,
        memory: Expr,
        host: Expr,
        initial_memory: PendingEquality,
        admitted: PendingEquality,
    ) -> Result<Initialization> {
        self.initialize_with_profile(
            assembler,
            model,
            arguments,
            memory,
            host,
            initial_memory,
            admitted,
            CoreLogicalEntryProfileV1::CFastV1,
        )
    }

    fn initialize_with_profile(
        &self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        arguments: Expr,
        memory: Expr,
        host: Expr,
        initial_memory: PendingEquality,
        admitted: PendingEquality,
        profile: CoreLogicalEntryProfileV1,
    ) -> Result<Initialization> {
        assembler.charge()?;
        let guard = self.admission_with_profile(model, arguments.clone(), profile)?;
        initial_memory.endpoints(
            &constant("Bool"),
            &Self::memory_admission(memory.clone()),
            &constant("Bool.true"),
        )?;
        admitted.endpoints(&constant("Bool"), &guard, &constant("Bool.true"))?;
        let owner = app("ir_byte_fresh_owner_v1", [memory.clone()]);
        let current = Current {
            frame: app(
                "IRFrame.mk",
                [
                    app("ir_func_id", [self.function.clone()]),
                    app("ir_func_entry", [self.function.clone()]),
                    nat(0),
                    app(
                        "ir_bind_params",
                        [
                            app("ir_func_params", [self.function.clone()]),
                            arguments.clone(),
                            list("IRBinding", &[]),
                        ],
                    ),
                    list("Nat", &[]),
                ],
            ),
            tail: list("IRFrame", &[]),
            legacy_memory: list("IRMemSlot", &[]),
            legacy_cursor: nat(0),
            world: app(
                "IRByteWorldV1.mk",
                [
                    model.world_type().clone(),
                    memory.clone(),
                    host.clone(),
                    list("Nat", std::slice::from_ref(&owner)),
                    app("Nat.succ", [owner]),
                ],
            ),
        };
        let initial = app(
            match profile {
                CoreLogicalEntryProfileV1::CFastV1 => "ir_byte_init_v1",
                CoreLogicalEntryProfileV1::RustU64LeafV1
                | CoreLogicalEntryProfileV1::RustU64AddLiteralV1 => "ir_rust_u64_init_v1",
            },
            [
                model.world_type().clone(),
                model.context().clone(),
                self.target.function_id.clone(),
                arguments.clone(),
                memory.clone(),
                host.clone(),
            ],
        );
        let no_globals = refl(
            &app("IRList", [constant("IRGlobal")]),
            list("IRGlobal", &[]),
        );
        let found = refl(
            &app("IROption", [constant("IRFunc")]),
            some("IRFunc", self.function.clone()),
        );
        let equality = PendingEquality::candidate(
            model.config_type(),
            initial,
            current.running(model),
            app(
                match profile {
                    CoreLogicalEntryProfileV1::CFastV1 => "ir_byte_init_current_v1",
                    CoreLogicalEntryProfileV1::RustU64LeafV1
                    | CoreLogicalEntryProfileV1::RustU64AddLiteralV1 => {
                        "ir_rust_u64_init_current_v1"
                    }
                },
                [
                    model.world_type().clone(),
                    model.context().clone(),
                    self.target.function_id.clone(),
                    arguments,
                    memory.clone(),
                    host.clone(),
                    self.target.binding.clone(),
                    self.target.signature.clone(),
                    self.function.clone(),
                    no_globals,
                    self.target.binding_found(),
                    self.target.signature_found(),
                    found,
                    initial_memory.term.clone(),
                    admitted.term,
                ],
            ),
        );
        let valid = PendingEquality::candidate(
            constant("Bool"),
            current.valid(model),
            constant("Bool.true"),
            app(
                "ir_byte_init_current_valid_v1",
                [
                    model.world_type().clone(),
                    memory,
                    host,
                    current.frame.clone(),
                    initial_memory.term,
                ],
            ),
        );
        Ok(Initialization {
            equality,
            current,
            valid,
        })
    }
}

#[cfg(test)]
#[path = "core_execution_initialization_tests.rs"]
mod tests;
