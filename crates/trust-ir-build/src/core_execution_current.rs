// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! A machine expression shared only during an immutable borrow of actual fields.

use super::{Expr, MachineModel, app, constant};
use std::ops::Deref;

/// Explicit current machine/world. A new state requires a new world-validity
/// fact; no cached pre-return validity is silently reused after a call/pop.
#[derive(Clone)]
pub struct Current {
    pub frame: Expr,
    pub tail: Expr,
    pub legacy_memory: Expr,
    pub legacy_cursor: Expr,
    pub world: Expr,
}

impl Current {
    pub fn machine(&self) -> Expr {
        app(
            "IRMachine.mk",
            [
                app(
                    "IRList.cons",
                    [constant("IRFrame"), self.frame.clone(), self.tail.clone()],
                ),
                self.legacy_memory.clone(),
                self.legacy_cursor.clone(),
            ],
        )
    }
    pub fn running(&self, model: &MachineModel) -> Expr {
        model.running(self.machine(), self.world.clone())
    }
    pub fn valid(&self, model: &MachineModel) -> Expr {
        model.valid(self.machine(), self.world.clone())
    }
}

/// Candidate syntax for this exact immutable borrow, never a validity fact.
/// No cache is installed on public mutable Current, so a later field mutation
/// cannot retain an earlier machine. The view cannot outlive its source borrow.
pub(super) struct SharedCurrent<'a> {
    source: &'a Current,
    machine: Expr,
}

impl Current {
    pub(super) fn shared_machine(&self) -> SharedCurrent<'_> {
        SharedCurrent {
            source: self,
            machine: self.machine(),
        }
    }
}

impl Deref for SharedCurrent<'_> {
    type Target = Current;

    fn deref(&self) -> &Current {
        self.source
    }
}

impl SharedCurrent<'_> {
    pub(super) fn machine(&self) -> Expr {
        self.machine.clone()
    }

    pub(super) fn running(&self, model: &MachineModel) -> Expr {
        model.running(self.machine(), self.source.world.clone())
    }

    pub(super) fn valid(&self, model: &MachineModel) -> Expr {
        model.valid(self.machine(), self.source.world.clone())
    }
}
