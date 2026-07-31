-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Lake build configuration for trust_ir-semantics Lean 4 formalization.
-- Depends ONLY on Lean core — no Mathlib (nothing under TrustIr/ imports it),
-- so `lake build` needs no `lake exe cache get` and no network.
--
-- Build: lake build
-- Check: lake env lean TrustIr.lean

import Lake
open Lake DSL

-- NOTE: Lean lake syntax uses backtick-quoted names.
-- These are Lean Name literals, not shell command injection.

package trust_irSemantics where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib TrustIr where
  srcDir := "."
