-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0

import TrustIr.Semantics.Memory

/-! The target-indexed image definitions are owned by `Semantics.Memory` so
memory operations can use them without a cycle. This module reexports that
surface for callers that name the target-model capability explicitly. -/
