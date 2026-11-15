# Contributing to TrustIr

TrustIr is a proof-carrying interchange format. Changes are welcome, but an IR
or proof-authority change usually spans more than the Rust type that first
exposes it.

## Build and test

Use the Trust toolchain (`targo`, `trustc`, `targo tippy`, `targo fmt`) from
[Trust](https://github.com/alabsystems/trust).
`targo --unverified` builds and tests without a proof claim; `targo trust
check` is the verified lane. TrustIr's 0.x line does not yet promise a minimum
supported Rust version.

Start with the narrowest crate or test that covers the change:

```bash
targo --unverified test --locked -p trust-ir
targo --unverified test --locked -p trust-ir-build
targo --unverified test --locked -p trust-ir-cli
targo --unverified test --locked -p trust-ir-conformance --test conformance
```

Before requesting review for a workspace-wide change, run the whole
workspace:

```bash
targo --unverified check --locked --workspace --all-targets --all-features
targo --unverified test --locked --workspace --no-fail-fast
```

The `frontend/` crate is intentionally outside the workspace. It uses
`rustc_private`, which the Trust toolchain's sysroot provides: build and test it
with `targo --unverified test --locked --manifest-path frontend/Cargo.toml`.
Changes to the Lean model should also run:

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

A new binary format version, a new tag in a wire enum, or a new `trust_ir.*.vN`
digest domain needs a row in `wire-allocations.toml`, added in the same change
as the code (`python3 scripts/wire_alloc.py reserve …`, then mark the row
`landed`; the file's header explains the rows). Wire versions land in number
order, so if an earlier reservation is still open, take the lowest open number
(`wire_alloc.py takeover`). The `binary::wire_census` tests and
`wire_alloc.py check` are executed tests and source scans, not proofs: they
fail a version constant in `binary.rs`, a tag byte of any wire enum the codec
source spells, or a version-suffixed identity string (`<name>.vN`,
`<name>-vN`) in non-test sources, that has no row. The registry's header says
where each of those scans stops. Name test and fixture files after the
feature, never the version number.

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
