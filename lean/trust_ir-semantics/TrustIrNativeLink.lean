-- Copyright 2026 Andrew Yates | Apache-2.0
-- Pure logical import: optimized code and initialization remain UNPROVED.
-- Lake supplies this empty module's native initializer from native/runtime_init.c.
-- Keep the logical import independent of the model DLLs: Lake preloads every
-- native import before this attachment. The complete provider initializes its
-- own model dependencies through initialize_TrustIrRuntime.
import Init
