# trust-ir-cli

Command-line inspector for TrustIr modules. Produces the `trust-ir` binary.

The CLI is a thin shim over crate APIs — it exists so downstream producers
(`tRust`, `clean`) and the consumer (`TrustCg`) can sanity-check modules
without writing a throwaway Rust harness for each operation.

## Installation

```sh
cargo build -p trust-ir-cli --release
# Binary at target/release/trust-ir
```

## Format detection

Format is auto-detected from the file extension, or passed explicitly with
`--format <bin|text|json|msgpack>`.

| Extension   | Format       | Backing crate feature |
|-------------|--------------|-----------------------|
| `.tmbc`     | Binary codec | `trust-ir/binary`     |
| `.trust_ir` | Text format  | `trust-ir/parser`     |
| `.json`     | JSON         | `trust-ir/serde`      |
| `.msgpack`  | MessagePack  | `trust-ir/serde`      |

Use `-` as the path to read a module from stdin.

## Exit codes

| Code | Meaning                                                           |
|------|-------------------------------------------------------------------|
| 0    | Success                                                           |
| 1    | Validation failure (for `validate`) or user error (bad arguments) |
| 2    | Parse / I/O / format error                                        |

## Subcommands

### `trust-ir validate <path>`

Runs `trust_ir_build::validate_module` and prints pass/fail. Exits 0 on success
and 1 if validation turns up any errors; errors are printed to stderr.

```sh
trust-ir validate ./build/mymod.tmbc
# ok: ./build/mymod.tmbc — module is well-formed

trust-ir validate ./build/broken.tmbc
# validation failed: ./build/broken.tmbc (1 error)
#   [0] BlockMissingTerminator(0)
```

### `trust-ir dump <path>`

Reads a module in any supported format and pretty-prints it in the canonical
text format to stdout.

```sh
trust-ir dump ./build/mymod.tmbc
# ; TrustIr text format v1
# module "test"
# ...
```

### `trust-ir convert --from <fmt> --to <fmt> <in> [<out>]`

Convert between binary / text / JSON / MessagePack. `<out>` defaults to
stdout. The `.tmbc` extension is the binary codec; `.trust_ir` is the canonical
text form.

```sh
# JSON for tool interop, then back to binary for the pipeline
trust-ir convert --from bin  --to json    mod.tmbc     mod.json
trust-ir convert --from json --to msgpack mod.json     mod.msgpack
trust-ir convert --from text --to bin     mod.trust_ir mod.tmbc
```

### `trust-ir show-gpu-eligibility <path> [--func <name>]`

For each function (or one named function), prints
`is_safe_for_gpu`, `is_gpu_eligible`, `divergence_class`, and the list of
GPU-relevant proof annotations.

```sh
trust-ir show-gpu-eligibility ./build/kernel.tmbc --func hot_loop
# function hot_loop
#   is_safe_for_gpu  = true
#   is_gpu_eligible  = true
#   divergence_class = uniform
#   gpu_proofs       =
#     - Pure
#     - NoPanic
#     - Deterministic
#     - ParallelMap
#     - DivergenceClass(Uniform)
```

## Design notes

* Zero new runtime deps on the `trust-ir` crate. The CLI pulls in `clap`,
  `serde_json`, and `rmp-serde` for its own wiring; the core crate remains
  dep-free by default (see the top-level `Cargo.toml` feature flag table).
* No semantic work. `trust-ir-cli` exits nonzero on validation failure — that
  is the only new "logic". Everything else delegates to `trust_ir::binary`,
  `trust_ir::parser`, `trust_ir::Display`, `serde_json`, `rmp-serde`, and
  `trust_ir_build::validate`.
* Follows the single-binary-with-verbs style established by
  `clean-cli`.

See issue #61 for the original spec and acceptance criteria.
