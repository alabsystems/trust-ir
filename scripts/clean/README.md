# Independent SemR export replay

These are data producers and regression inputs, not trusted proof checkers.
Use the exact `lean/semr/lean-toolchain` toolchain and official
`leanprover/lean4export` commit
`12581a6b680d8478175596338eb2d53383a323e3` (export format 3.1.0).
Fetch GitHub inputs through `aterm agh`. Build the exporter separately; do not
add it to SemR's mathematical imports. Keep output outside the checkout.

With `LEAN_BIN` the pinned toolchain's `bin`, `EXPORTER` its separately built
exporter checkout, and `OUT` an owned external output directory:

```sh
export PATH="$LEAN_BIN:$PATH"
# First build lean/semr with this toolchain's lake and the host's real linker.
export LEAN_PATH="$EXPORTER/.lake/build/lib/lean:$PWD/lean/semr/.lake/build/lib/lean"
"$LEAN_BIN/lean" --run scripts/clean/ExportSemR.lean "$OUT/inventory.json" > "$OUT/semr.ndjson"
env -u LEAN_PATH clean olean replay --from-export "$OUT/semr.ndjson" \
  --max-heartbeats 2000000 --json > "$OUT/replay.json"
```

Apply the host's resource admission wrapper to compilation/export/replay.
The exporter visits **all** imported constants, including internal names.
Stock `dumpConstant` excludes unsafe declarations; the inventory retains
their flags. Partial declarations remain exported and must be accounted for
in the checker result. Importing `SemRMemory` and `SemRMiniRust` covers the
four current SemR/MiniRust model modules and their standard-library closure;
it does not cover the separate frame/formal packages or a native producer.

For the smaller string-reduction regression, copy `StringReduction.lean` to
`OUT`, compile it there with the pinned Lean, then export its five declarations:

```sh
(cd "$OUT" && "$LEAN_BIN/lean" -o StringReduction.olean StringReduction.lean)
export LEAN_PATH="$EXPORTER/.lake/build/lib/lean:$OUT"
"$LEAN_BIN/lean" --run "$EXPORTER/Main.lean" StringReduction -- \
  CleanReplayProbe.natControl CleanReplayProbe.stringControl \
  CleanReplayProbe.appendLoad CleanReplayProbe.appendStore \
  CleanReplayProbe.interpolateLoad > "$OUT/string.ndjson"
env -u LEAN_PATH clean olean replay --from-export "$OUT/string.ndjson" \
  --max-heartbeats 2000000 --json > "$OUT/string-replay.json"
```

Retain actual process exit codes. Exit 1 is rejection and exit 2 is decline;
neither establishes acceptance. Do not discard refused imports, skip partial
declarations, use trusted-import replay, or raise budgets to manufacture a
passing closed-environment result. Even an accepted export needs a separately
stated axiom/opaque policy before qualifying the stricter reference entry.

Measured results and exact tool/input identities are in
`reports/2026-11-12-clean-current-semr/README.md` in the development tree.

The inventory now uses schema 2 and includes typed name components. Lean's
displayed names and Clean's escaped report names differ; comparing display
strings silently loses coverage. After replay, capture its actual exit and audit
the inventory/report correspondence:

```sh
env -u LEAN_PATH clean olean replay --from-export "$OUT/semr.ndjson" \
  --max-heartbeats 2000000 --json > "$OUT/replay.json"
replay_exit=$?
python3 scripts/audit_clean_semr_replay.py --inventory "$OUT/inventory.json" \
  --report "$OUT/replay.json" --process-exit "$replay_exit" > "$OUT/coverage.json"
```

Run the audit even after nonzero replay exits; a shell using `set -e` must
capture the status explicitly. The audit refuses lossy inventory, duplicate or
foreign identities, missing safe declarations, inconsistent counts/status,
partial disposition changes, and all refusals/exhaustions/skips. Unsafe
exclusions are reported separately. This only audits the supplied evidence;
it cannot authenticate JSON, check a proof, or grant stricter axiom-policy authority.

`KernelReduction.lean` further isolates the two failure families. Compile/export
it in the same way as the small string fixture, selecting these eight names:

```text
CleanReductionProbe.PolyStep.ctorElimType
CleanReductionProbe.MonoStep.ctorElimType
CleanReductionProbe.OneParam.ctorElimType
CleanReductionProbe.directAppend
CleanReductionProbe.emptyAppend
CleanReductionProbe.toStringLiteral
CleanReductionProbe.natBeta
CleanReductionProbe.charListLiteral
```

The two polymorphic eliminators and three direct string computations are
refused by installed Clean; the monomorphic eliminator, `toString` and arithmetic
controls pass. This fixture is diagnostic, not a passing acceptance subset.
