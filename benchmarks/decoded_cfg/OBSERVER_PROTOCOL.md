# Decoded CFG phase observer protocol

This observer adds the optional
`trustir_cfg_bench` target rooted at `Tools.DecodedCFGBenchmark`; the default
library and production oracle targets remain unchanged. Its product baseline is
published `348424bd26baea729a9d5c5837730b1356043bdd`, normally merged with support
`f871b2227868fb6e81ab7b9907785637be89d99e`. That support's historical Rust reference
product is `497b26aab1b1a6dd160cb91f3cef1b4f9ea64528`; its original packet and inputs
are immutable. Current builds and executions need separate source-bound records.

Before any native baseline or candidate measurement, compile and inspect the
actual observer C, freeze the observer/input/tool/source identities, and save both
endpoint executables. The older plan's `1fe` product label is historical. Neither
the `497b` Rust reference executable nor earlier lookup timings qualify a newer
native baseline. The original source-only packet contains no compilation,
executable run, timing or C inspection; later records must state their exact cut.

The CLI is:

```text
trustir_cfg_bench REQUEST.json INVENTORY.json CASE_KEY WARM_REPETITION_COUNT COLD_PREPARATION_COUNT
```

The future driver authenticates the fixed V2 inventory, its selected case hash,
and the cold carrier bytes before launching the observer. The observer reads the
case's actual `[last, missing, first]` metadata, requires one function-0 definition
and one argument-free run with an empty choice tape, checks the source row count
and endpoint IDs, and verifies missing-key absence. It requires request fuel
20000/depth 8. The 66 V2 cases and all 330 cold carriers have Rust reference
validation/execution evidence at the older product cut documented in README;
this observer does not replace a validator or assert an execution result.

File reads, JSON text parsing, metadata checks, one actual module decode, one
actual context preparation, and the forced actual `ctx.functions 0` lookup occur
before the phase timers. Warm queries use that held `EvalFunction.cfg`, including
actual presence checks before timing. There is no model index or constant-result
lookup. Every warm repetition performs exactly three queries, in metadata order.
The output reports `warm_loop_repetitions` and the separate
`warm_query_count = warm_loop_repetitions * 3`.

| Phase | Inside the timer | Result checksum and retention |
| --- | --- | --- |
| `decode_retained` | Actual `TrustIrEval.module` calls on JSON obtained from an opaque IO.Ref each iteration, Array pushes of complete decoded modules, one retaining Ref store | After STOP, an opaque Ref read recovers the complete Array; the checksum consumes each decoded function's ID, entry and block census. `retained_checksum` records Array size. Release follows this read and observation. JSON text parsing is excluded. |
| `context_retained` | Actual `contextOf source (8 + i % 2)` calls, including its inference/context work, Array pushes of complete contexts, one retaining Ref store | The complete Array survives STOP and a post-STOP opaque Ref read. Its checksum consumes each actual context's depth; `retained_checksum` records Array size. Release follows this observation. No lookup probe occurs in the construction loop. |
| `context_lifecycle` | Actual context construction with depth `8 + i % 2`, an ID-0 function/error/declaration mixed probe, checksum reduction and context release | The checksum consumes actual context depth and actual lookup results. There is no retained context Array in this phase. The phase is construction/probe/release, not pure construction. |
| `warm_cfg` | The held actual CFG is queried for all three metadata keys per repetition; the checksum consumes returned block parameter/body/result-destination census, or zero for absence | The whole converted function, including its CFG closure, is retained in a Ref through STOP. A post-STOP opaque Ref read produces a separately reported header marker. No decode or context construction occurs in this phase. |

Every phase has its own `checksum` and `retained_checksum` fields. There is no
aggregate checksum and no cross-phase equivalence claim. Timing values exclude
the post-STOP checksum walks and retention markers described above. Constructor
depth variation is an anti-hoisting dependency for preparation; it does not alter
the frozen request execution depth. Cold retained timings include Array/Ref
overhead and lifecycle includes a lookup probe and release. They are not isolated
allocator or inference-only timings.

Any eventual peak RSS observation covers the entire process: parsed request and
inventory, preflight module/context, all phases, retained Arrays, checksum walks,
and runtime/tool overhead. It is not phase-local memory or an allocation count.
Phase order is decode, retained context, lifecycle, warm CFG. No subtraction of
those phases is justified as an isolated compiler cost.

`check_observer_source.py` checks source markers/order, the optional-target-only
lakefile delta, and unchanged original/V2 request identities. Its negative
controls detect specified source-protocol mistakes. It does not elaborate Lean,
inspect generated C, prove object lifetimes, or measure anything. Required later
C inspection must verify actual per-iteration module decoding/context preparation,
one retained actual function outside warm timing, real CFG calls inside the warm
loop, and retention/releases on the intended sides of STOP. An initially compiled
observer that fails these checks earns no timing credit; preserve its source/C
diagnostics rather than changing the frozen input cohort silently.

Complete oracle outputs must agree before timing claims. Interleave baseline and
candidate endpoints in a declared timing window with host-load snapshots, retain
cold/tiny/retained-construction/lifecycle/RSS regressions, and report measured
tradeoffs by source cut. A warm-query improvement does not establish a universal
or whole-program speedup, and no measurement grants native or proof authority.
