# trust-ir-cli

Command-line inspector for TrustIr modules. Produces the `trust-ir` binary.

The CLI is a thin shim over crate APIs — it exists so downstream producers
(`tRust`, `clean`) and the consumer (`TrustCg`) can sanity-check modules
without writing a throwaway Rust harness for each operation.

## Installation

```sh
targo --unverified build -p trust-ir-cli --release
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

Flags:

| Flag | Effect |
|------|--------|
| `--format <bin\|text\|json\|msgpack>` | Explicit format override (auto-detected from the extension by default). |
| `--no-giveback` | Skip the give-back certification pass. That pass is **ON by default**: every `&mut` function whose backward function is kernel-certifiable is reported, with no annotations required. |
| `--lineage <MANIFEST>` | Check proof-lineage closure (Interpretation B) against a sidecar manifest (`.tmpl` binary or `.json`): structural validation against the module's proof tables plus the validator-authority closure walk. Exits 1 on an open, non-replayable, or mis-threaded lineage. |
| `--forbid-trusted` | The zero-`Trusted` census gate: list every obligation whose status is `Trusted` and every certificate whose evidence is `Trusted`, and exit 1 if any exist. |
| `--forbid-failed` | The violated-contract build-abort gate: list every obligation whose status is `Failed` and exit 1 if any exist. |

```sh
trust-ir validate ./build/mymod.tmbc
# ok: ./build/mymod.tmbc — module is well-formed

trust-ir validate ./build/broken.tmbc
# validation failed: ./build/broken.tmbc (1 error)
#   [0] BlockMissingTerminator(0)
```

**Allocation-size advisory.** `validate` also reports, on stderr, every
`Alloca` / `HeapAlloc` whose byte size is not provably within the largest
object the module's target can hold — `isize::MAX` bytes at its pointer width;
there is no other threshold — on every target, inside or outside the
canonical scalar-alignment table. An allocation every execution of which asks
for more prints as a `warning:` (it can never succeed); one whose size no bound
keeps within the line, or whose element type has no byte size, prints as a
`note:` line, every one of them. Silence is not a statement that an allocation
is small: only defined executions are judged (a zero or negative count is
undefined behaviour at the allocation, so an unchecked `i64` count of bytes,
at most `i64::MAX`, is within a 64-bit line), and a count narrower than the
pointer is bounded by its type (`u32` elements of `u64`, up to 32 GiB, are not
reported). The advisory never changes the exit code. `trust_ir::alloc_bound`
documents the analysis.

```sh
trust-ir validate ./build/alloc.trust_ir
# note: 1 allocation whose size no bound keeps within the target's largest object (advisory):
#   alloca of `i64` in `f` bb0: no bound proves its size within the target's 9223372036854775807-byte object limit; bound the count (`if n <= MAX`), mask it (`n & MASK`) or narrow it (advisory)
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

### `trust-ir run <paths>... [--entry <name>]`

Links one or more modules into an executable image and runs a function under
the reference interpreter, printing its return value(s). A directory argument
expands to its `*.trust_ir` modules. Functions are linked by name: definitions
win over declarations, identical duplicate definitions are deduped, and
conflicting definitions are an error. Externs that remain bodyless become
interpreter builtins (Rust allocator shims, `mem*`, a few `core::intrinsics`
bit ops) or trap stubs that fail with the extern's name when reached.

| Flag | Default | Effect |
|------|---------|--------|
| `--format <fmt>` | auto-detect | Format override for FILE arguments; directories always scan `.trust_ir` text modules. |
| `--entry <name>` | `program` | Entry function name. |
| `--fuel <n>` | `1000000000` | Interpreter fuel (instruction budget). |
| `--max-call-depth <n>` | `4096` | Maximum interpreted call depth. |
| `--validate` | off | Also validate the linked image before executing. |

```sh
trust-ir run ./build/emit-each/ --entry main --validate
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

### `trust-ir spec-link <path>`

Runs the spec↔source cross-reference pass over a module's `SpecModule`
objects. Prints a per-machine coverage report and enforces structural
identity/ownership/typed resolution (S0/S1/S2), closure and coverage
(Ob.1/Ob.3/Ob.4), proof resolution against a valid manifest (L1), and a
nonblank projection (L2). Exits 0 only for a certifying `Linked` report.

| Flag | Effect |
|------|--------|
| `--format <fmt>` | Explicit format override. |
| `--harness-manifest <PATH>` | JSON manifest listing the real `#[kani::proof]` harnesses. Enables L1 proof-name resolution: every `SpecProof`'s `proof_name` must resolve to an entry here. |
| `--require-manifest` | Require a manifest even for `DesignOnly` proof bindings. `Linked` bindings already require one by default. |
| `--allow-unverified-proofs` | Analyze `Linked` proof bindings without a manifest. The result is explicitly non-certifying and exits nonzero even when no obligation violation is found. Conflicts with the two flags above. |

### `trust-ir --version` / `trust-ir version [--json]`

`--version` (`-V`) prints the build identity,
`trust-ir <MAJOR.MINOR.0>+<source>`. `<source>` is `g<12-hex>` (packaging set
`ALAB_BUILD_GIT_SHA` and attested a clean tree with
`ALAB_BUILD_GIT_DIRTY=0`; the `TRUST_BUILD_GIT_*` spelling is refused because
verified Targo scrubs `TRUST_*` from build scripts), `g<12-hex>.dirty`, `g<12-hex>.local` (read by
`git` from the crate's own checkout; the working tree is not attested), or
`unknown`. It is never a guessed sha. `--version --verbose`, or the `version`
subcommand, adds the full sha and its attestation, the wire version and
readable range, and the module-identity digest domain. `version --json` emits
the same facts as JSON. All of it comes from `trust_ir::BUILD_IDENTITY`,
which is resolved by `crates/trust-ir/build.rs`.

```sh
trust-ir --version --verbose
# trust-ir 0.14.0+g0123456789ab
# source 0123456789ab (packaged; working tree attested clean)
# wire v46; reads v23..=v25, v29..=v46 (v26..=v28 refused: ambiguous lineage)
# module identity domain trust_ir.module.v3
```

## Design notes

* Zero new runtime deps on the `trust-ir` crate. The CLI pulls in `clap`,
  `serde_json`, and `rmp-serde` for its own wiring; the core crate remains
  dep-free by default (see the feature table in the root `README.md`, and the
  `[features]` section of `crates/trust-ir/Cargo.toml` for the authoritative
  list).
* No semantic work. `trust-ir-cli` exits nonzero on validation failure — that
  is the only new "logic". Everything else delegates to `trust_ir::binary`,
  `trust_ir::parser`, `trust_ir::Display`, `serde_json`, `rmp-serde`, and
  `trust_ir_build::validate`.
* Follows the single-binary-with-verbs style established by
  `clean-cli`.

See issue #61 for the original spec and acceptance criteria.
