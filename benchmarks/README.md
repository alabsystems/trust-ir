# Benchmarks

Two TrustIr benchmark fixture crates — workspace members that generate large
TrustIr modules to stress-test the build / validate / serialize pipeline. Each
is a small `clap`-based binary that builds a module with `trust-ir-build` and
writes it to disk via `trust_ir::binary::serialize_module`.

| Crate | Package | What it generates |
|-------|---------|-------------------|
| `benchmarks/supremacy-fixture` | `supremacy-fixture` | A large CHC transition module — a chain of basic blocks (default 10,000), to stress the IR pipeline at scale. |
| `benchmarks/raft-fixture` | `raft-fixture` | A TLA+ Raft grid-parallel synthesis module. |

## Running

```bash
# Supremacy: default 10,000 blocks, override with --states
targo --unverified run -p supremacy-fixture -- --states 10000 --output supremacy.tmbc

# Raft
targo --unverified run -p raft-fixture -- --output raft.tmbc
```

Each binary writes a binary-format (`.tmbc`) TrustIr module to the `--output`
path and prints progress to stdout. Validate or inspect the result with the CLI:

```bash
targo --unverified run -p trust-ir-cli -- validate supremacy.tmbc
targo --unverified run -p trust-ir-cli -- dump supremacy.tmbc
```

## Notes

- The previous top-level `run_eval.sh` Docker harness was removed as broken
  template cruft; these fixtures are plain workspace binaries with no Docker or
  external-runner dependency.
- The fixtures generate structurally simple modules (e.g. the supremacy chain
  is a sequence of near-empty blocks). They measure pipeline throughput, not
  realistic program shapes; do not read them as semantic workloads.
