This integration workspace runs the seven source-value checker tests and the
complete ten-test actual-producer corpus. It is outside the default library
test discovery because the producer modules bind a specific kernel environment.
All ten producer tests remain required evidence for actual Trust toolchain
integration; they have no ignored cases or runtime skips.
The harness's default clean-tv-anchor feature forwards to the implemented
trust-ir-build feature, preserving the unchanged test files' original guards.

Run from an owned TrustIR checkout with a frozen, already prepared Trust stage
source tree and an owned dependency cache:

```sh
python3 scripts/test_source_value_stage.py \
  --trust-root /path/to/owned/trust \
  --cargo-home /path/to/owned/cargo-home \
  --output /path/to/owned/trust-ir/target/source-value-stage-run.noindex
```

The runner copies the current materialized TrustIR sources, checks their byte
identity, and derives the existing stage patch tables from Trust's Cargo.toml.
Only self-IR paths change to select that source copy. The generated integration
manifest requests the exact Clean kernel path and features already requested
by the stage workspace. It uses a normal, private development Cargo.lock, then
runs locked/offline tests through the canonical build slot and Trust wrapper.
The canonical TrustIR and Trust manifests and lockfiles remain unchanged. The
output retains the source map, resolved dependency/feature identities, raw logs,
development lock and result. A missing prerequisite or context mismatch fails
the run; the runner neither replaces a digest nor regenerates a proof fixture.

The first standalone run with the canonical Clean 7f25 dependency passed three
producer tests and failed seven: its environment binding differed, and its
prelude lacked instHShiftRight. Those failures remain genuine compatibility
evidence. The unchanged ten tests passed with the existing stage Clean 6521
source and its math-overlays/farkas-constructive feature closure. This separate
context result does not make the canonical run pass or establish general
artifact interchangeability.

The canonical default API and its seven self-contained tests do not require
this stage profile. Production's separate `source-value-operational` feature
exposes checked straight-line U64/U32 and full-runtime-context U32 APIs. This
stage runner does not enable or exercise those APIs. The two data-test lanes
supply no source-generation authority, body license, ABI/NoUB assurance or
machine-code proof; the operational APIs retain their own checked scope.
