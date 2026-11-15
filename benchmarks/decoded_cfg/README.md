# Decoded CFG reference inputs

This support cohort validates requests and retains cold carrier bytes for a future
decoded-CFG lookup comparison. It changes no interpreter, optimizer, fuel default,
proof policy, or native authority. No Lean oracle, native oracle, or timing job was
run for this support qualification.

The original `generate.py`, `proposed-requests/inventory.json`, helper, and all 66
requests preserve the prototype bytes. The generator's helper source is immutable
`1fe526c1848377ce9423297f10458c6bd06f7870`; the Rust reference runs used product
source `497b26aab1b1a6dd160cb91f3cef1b4f9ea64528`.

| Input | SHA-256 |
| --- | --- |
| Original generator | `9d02a497ee260d124ed9bf47dee461a93d40741e279ebf5dbfd0a468ff6f3094` |
| Original inventory | `6d2bf2a528c0c5b3d9fd6f7b8f96dcccf5e1344a054027c22da63fdeaeaeff94` |
| Original helper | `df5db63e73bbf5491e922b228a7a9871eed6abf194043caca09ca671fb3556d8` |
| V2 derivation | `3e0cea67af8cee981f58818dbd68ed53d7bdf37f8d71d0d2be3b14690f0e1b62` |
| V2 inventory | `ab551e29400bdc25ae4cec2875755236473145690dfe1750fd23c4d15c657906` |

The requests cover both pointer widths, 1/2/4/8/64/512/4096 blocks, and loop counts
0/1/1000 where the shape supports a loop. There are 34 dense and 32 sparse cases.
The sparse IDs include `4294967295`. Source rows retain their generated order;
execution branches through a different order. This is not an additional cohort
with numerically permuted source IDs. Every module has one function, ID 0, and one
argument-free run.

`derive_reference_fuel.py` authenticates the original inventory and each request,
then changes only the exact request byte sequence `"fuel":10000` to `"fuel":20000`. Depth stays
8. All module bytes and every other request byte remain unchanged. V2 is a separate
input cohort, not a production-budget change. The largest successful reference
paths use 10,099 instruction steps (`4096 + 6 * 1000 + 3`).

Run the example through the repository's explicit unverified Rust lane, with an
owned cache and `SDKROOT` absent inside the resource lease:

```sh
scripts/run-targo.sh run --locked -p trust-ir-conformance \
  --example decoded_cfg_inputs -- benchmarks/decoded_cfg/proposed-requests \
  OUTPUT_V1 --original-resource-controls
scripts/run-targo.sh run --locked -p trust-ir-conformance \
  --example decoded_cfg_inputs -- benchmarks/decoded_cfg/fuel-adjusted-requests OUTPUT_V2
```

Each module is validated with `validate_module` before reference execution. The
example preserves original bytes and produces binary, JSON, MessagePack, and
checked-text carriers, decodes them, compares the complete module AST and explicit
function/block IDs and order, validates again, and executes with the request's fuel
and depth. Each successful return is compared to exactly `[I32(42)]`, including
type, integer width/signedness/raw value, return count 1, and host-call count 0.
Checked-text losses are retained as non-executed refusals if encountered.

The qualified results at the source cut above are:

| Cohort | Valid source modules | Valid carriers | Exact `[I32(42)]`, no host calls | Reference-only out of fuel | Checked-text refusals | Unexpected failures |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Original: fuel 10000, depth 8 | 66 | 330 | 310 | 20 | 0 | 0 |
| V2: fuel 20000, depth 8 | 66 | 330 | 330 | 0 | 0 | 0 |

All five carriers preserve the complete module AST for every source, including
all 32 sparse cases. The 20 original resource controls are four source requests
across five carriers. Their `OutOfFuel` observations carry no expected-value
success credit and no claim that different engines count fuel equally. The JSON
field `value_admission_credit` only distinguishes exact reference-value successes
from those resource controls; it grants no producer or proof authority.

The scoped example passes Tippy with `-D warnings`. Initial cache-ownership refusal
and an earlier diagnostic that used the Rust default depth 64 remain historical
zero-credit diagnostics; the table uses the corrected actual depth-8 executions.
No runtime source, native oracle, timing result, or optimization claim follows
from these reference and carrier checks.
