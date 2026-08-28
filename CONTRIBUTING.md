# Contributing to TrustIr

TrustIr is a proof-carrying interchange format. Changes are welcome, but an IR
or proof-authority change usually spans more than the Rust type that first
exposes it.

## Build and test

Use a current stable Rust toolchain. TrustIr's 0.x line does not yet promise a minimum
supported Rust version.

Start with the narrowest crate or test that covers the change:

```bash
cargo test --locked -p trust-ir
cargo test --locked -p trust-ir-build
cargo test --locked -p trust-ir-cli
cargo test --locked -p trust-ir-conformance --test conformance
```

Before requesting review for a workspace-wide change, run the public release
shape:

```bash
cargo check --locked --workspace --all-targets --all-features
cargo test --locked --workspace --no-fail-fast
```

The `frontend/` crate is intentionally outside the workspace. It uses
`rustc_private` and needs a compiler-internal toolchain built from a compatible
Trust/Rust tree; a stock Rust installation is sufficient for the exported
workspace but not for that driver. Changes to the Lean model should also run:

```bash
(cd lean/trust_ir-semantics && lake build)
```

The maintainer gates in `scripts/` combine schema parity, proof-state censuses,
lineage checks, conformance, the non-default AY adapter, and optional Lean
checks. Some combined-tree checks require the exact sibling revisions recorded
by the maintainers.

## Change discipline

An IR-schema change should update every affected:

- Rust type, builder, validator, parser/formatter, codec, and interpreter path;
- binary version gate and compatibility test;
- byte-golden conformance fixture and migration behavior;
- Lean name-parity or semantic surface;
- producer/consumer contract and public format documentation.

A proof-authority change must include a negative case. Unsupported, stale,
forged, dangling, misbound, or faith-stamped evidence must fail at the exact
authority level being claimed. A green structural validation result is not a
substitute for the checker designated by the evidence kind.

Keep commits focused and explain the claim being changed, its trusted boundary,
and how the new tests would fail under the old or forged behavior. Do not
commit generated build directories, credentials, private machine paths, or
session artifacts.

## Licensing and conduct

TrustIr is licensed under Apache-2.0. Contributions are accepted under the same
terms (inbound equals outbound): by submitting a change, you agree that it is
licensed under Apache-2.0.

Participation is governed by [`CODE_OF_CONDUCT.md`](CODE_OF_CONDUCT.md).
Bugs and usage questions belong in the channels described by
[`SUPPORT.md`](SUPPORT.md); suspected vulnerabilities use the private process
in [`SECURITY.md`](SECURITY.md).
