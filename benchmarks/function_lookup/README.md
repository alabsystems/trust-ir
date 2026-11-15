# Current-source function lookup measurements

This support was added to exact published
`cb4b0fe5f3ea89be0ea659b7abe0bfa7a5276384` before any lookup Core edit.
Its original oracle was built from an empty Lake cache, with SDKROOT cleared
inside a six-CPU lease, and copied outside the tree. SHA-256:
`9cb303d49ab67b60ebf672648f2a9b19aa9ab662d8cb3274555ade4202a71a29`.
All 21,345 original tracked path/mode/blob/SHA records bookended unchanged.
The old0611→d893 packet remains historical and supplies no current timing credit.

`generate.py` creates48 deterministic requests on both pointer widths, with
dense/sparse IDs, direct-call loops, short SeqMap, and zero/one cases. Actual
warm queries are `[last source function ID, 4294967294, 0]`, recorded in the
inventory and printed by the native tool. The Rust example validates/reference
executes220 cold-carrier cases;20 checked-text sparse-ID refusals stay separate.
Its builds/reference execution use the explicit unverified Targo lane.

The optional `trustir_lookup_bench` measures actual contextOf and its public
lookup fields. An IO.Ref retains the context through every warm stop timestamp,
including the last mixed loop; post-timestamp reads make retention explicit.
The retained-constructor timer stores all new actual contexts until after stop.
It includes retention-array and one ref-store overhead, but no query probe or
context release. The separate lifecycle timer includes construction, one mixed
ID0 probe, and release each iteration. Retained-constructor RSS reflects its
intentional context count and is separate from whole-oracle endpoint RSS.
Generated C is inspected on both sides to verify these ownership/timer positions.

Drivers retain fixed request/executable/source hashes, consumed checksums,
machine/process conditions, timings and peakRSS. Run heavy commands through
build-slot. These observations imply no universal speedup, total interpreter
cost bound, or native/source/compiler/proof authority. Tiny and cold regressions
must be reported alongside warm and connected-call gains.
