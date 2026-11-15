-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Root of the W5b Lean-execution oracle library (roadmap WS2.19): the
-- serde-JSON decoder and the batch runner behind the `trustir_eval`
-- executable. Kept OUTSIDE the `TrustIr` semantics library: it imports
-- `Lean.Data.Json`, which the axiom-audited semantics never do, and nothing
-- under `TrustIr/` imports it.

import TrustIrEval.Decode
import TrustIrEval.Run
